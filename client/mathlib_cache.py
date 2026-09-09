"""Machine-local shared Mathlib (dependency) store — dedupe the big, identical
`.lake/packages` across a project's workspaces.

Every Choir workspace for a project pins the same dependency set (its committed
`lake-manifest.json`), so each one's `.lake/packages` — Mathlib + transitive
deps, several GB of byte-identical oleans — is the same. Fetching it per
workspace (`lake exe cache get`) costs N × several GB and fills disks fast (the
v0 behaviour).

Instead Choir keeps ONE prebuilt copy per dependency-set under
`~/.choir/mathlib-store/<key>/` and populates each workspace from it with a
copy-on-write clone (APFS `clonefile` / `cp --reflink`): near-zero extra disk,
because dependency oleans are never modified in place. So N workspaces cost
~one copy total instead of N. The store is keyed by the *resolved dependency
set* (the manifest's package revs, not its raw text — see `manifest_key`), so
two different projects pinning the same Mathlib share one entry, while a
toolchain/Mathlib bump changes a rev and transparently gets a fresh store.

Degrades cleanly: if the filesystem can't reflink, it falls back to a normal
per-workspace `lake exe cache get` (correct everywhere, space-saving where the
FS supports COW). The store under `~/.choir/mathlib-store/` is cache-like —
safe to delete between projects to reclaim space.
"""

from __future__ import annotations

import hashlib
import json
import os
import platform
import shutil
import subprocess
import sys
from collections.abc import Callable
from pathlib import Path

MANIFEST_NAME = "lake-manifest.json"
PACKAGES_REL = Path(".lake") / "packages"


def store_root() -> Path:
    """Root of the shared dependency store. `$CHOIR_MATHLIB_STORE` overrides."""
    override = os.environ.get("CHOIR_MATHLIB_STORE")
    if override:
        return Path(override).expanduser()
    return Path.home() / ".choir" / "mathlib-store"


def _dep_signature(manifest_text: str) -> str | None:
    """Canonical JSON of the *resolved dependency set* — for each package its
    `name`, `url`, `rev`, `subDir` — sorted and order-independent. Returns None
    if the manifest isn't the expected JSON shape, so the caller falls back to
    raw-text hashing.

    Deliberately excludes everything project-specific: the manifest's root
    package `name`/`lakeDir`/`packagesDir`/`version` and each dep's `inputRev`
    (how the pin was spelled) and `inherited`/`scope`. None of those change the
    bytes in `.lake/packages`; the resolved `rev` (a git SHA) does. So two
    different projects pinning the identical deps produce the same signature.
    """
    try:
        data = json.loads(manifest_text)
        packages = data["packages"]
    except (json.JSONDecodeError, TypeError, KeyError):
        return None
    if not isinstance(packages, list):
        return None
    deps: list[dict[str, object]] = []
    for pkg in packages:
        if not isinstance(pkg, dict):
            return None
        deps.append({k: pkg.get(k) for k in ("name", "url", "rev", "subDir")})
    deps.sort(key=lambda d: tuple(str(d[k] or "") for k in ("name", "url", "rev", "subDir")))
    return json.dumps(deps, sort_keys=True)


def manifest_key(manifest_text: str) -> str:
    """Stable key for a dependency set = hash of its resolved deps.

    Keys on the dependency set (`_dep_signature`), not the raw manifest text,
    so two DIFFERENT projects that pin the identical Mathlib + transitive deps
    share ONE store entry instead of each keeping a multi-GB copy. A
    toolchain/Mathlib bump changes a `rev`, which changes the key → fresh store
    entry. Non-standard manifests fall back to raw-text hashing (distinct raw
    inputs stay distinct)."""
    signature = _dep_signature(manifest_text)
    payload = signature if signature is not None else manifest_text
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()[:16]


def _packages_present(pkgs: Path) -> bool:
    return pkgs.is_dir() and any(pkgs.iterdir())


def reflink_tree(src: Path, dst: Path) -> bool:
    """Copy-on-write clone the directory tree `src` → `dst`. True on success.

    macOS: `cp -cR` (clonefile). Linux: `cp -a --reflink=always` (fails loudly
    on a non-reflink filesystem so the caller falls back rather than silently
    making a full, space-wasting copy). `dst` must not already exist; a partial
    `dst` is cleaned up on failure so a fallback path starts clean.
    """
    if dst.exists():
        return False
    dst.parent.mkdir(parents=True, exist_ok=True)
    if platform.system() == "Darwin":
        cmd = ["cp", "-cR", str(src), str(dst)]
    else:
        cmd = ["cp", "-a", "--reflink=always", str(src), str(dst)]
    try:
        result = subprocess.run(cmd, capture_output=True, text=True, check=False)
    except FileNotFoundError:
        return False
    if result.returncode == 0:
        return True
    if dst.exists():
        shutil.rmtree(dst, ignore_errors=True)
    return False


def _default_cache_get(workspace: Path) -> bool:
    """Run `lake exe cache get` in `workspace` to materialise + fetch deps."""
    try:
        result = subprocess.run(
            ["lake", "exe", "cache", "get"],
            cwd=workspace,
            capture_output=True,
            text=True,
            check=False,
        )
    except FileNotFoundError:
        print("mathlib-cache: `lake` not found; skipping dep prefetch", file=sys.stderr)
        return False
    if result.returncode != 0:
        print(
            "mathlib-cache: `lake exe cache get` failed: "
            f"{(result.stderr or '').strip()[:200]}",
            file=sys.stderr,
        )
        return False
    return True


def prepare_workspace_deps(
    workspace: Path,
    *,
    cache_get: Callable[[Path], bool] | None = None,
) -> str:
    """Ensure `<workspace>/.lake/packages` is populated, sharing via the store.

    Idempotent and best-effort — never raises; on any failure it returns a
    status and lets the normal `lake exe cache get` proceed. Returns:

      ``"no-manifest"``      not a Lake/Mathlib project — nothing to do
      ``"present"``          packages already there (resume / re-run)
      ``"hit"``              COW-cloned from the shared store (near-zero disk)
      ``"fetched"``          miss: fetched, then saved to the store for reuse
      ``"fetched-nostore"``  miss: fetched, but couldn't save (no reflink)
      ``"skipped"``          fetch unavailable/failed — the build will handle it

    `cache_get(workspace) -> bool` runs the fetch (injected in tests).
    """
    manifest = workspace / MANIFEST_NAME
    if not manifest.is_file():
        return "no-manifest"

    pkgs = workspace / PACKAGES_REL
    if _packages_present(pkgs):
        return "present"

    key = manifest_key(manifest.read_text(encoding="utf-8"))
    store_pkgs = store_root() / key / PACKAGES_REL

    # HIT: clone the prebuilt deps from the store — no fetch, near-zero disk.
    if _packages_present(store_pkgs):
        if reflink_tree(store_pkgs, pkgs):
            print(f"mathlib-cache: shared deps from store [{key}] — no fetch needed")
            return "hit"
        print("mathlib-cache: store present but reflink unavailable; fetching")

    # MISS: fetch, then save to the store so the next workspace is a HIT.
    fetch = cache_get if cache_get is not None else _default_cache_get
    if not fetch(workspace) or not _packages_present(pkgs):
        return "skipped"
    if not store_pkgs.exists() and reflink_tree(pkgs, store_pkgs):
        print(f"mathlib-cache: saved deps to store [{key}] for reuse")
        return "fetched"
    return "fetched-nostore"
