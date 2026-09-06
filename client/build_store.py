"""Machine-local shared store for a project's OWN build oleans (`.lake/build`).

Sibling to `client.mathlib_cache` (which shares the DEPENDENCY oleans in
`.lake/packages`, keyed by manifest hash). This one shares the project's own
`.lake/build`, keyed by (pinned commit, toolchain) — source-specific oleans
must not be keyed by manifest. Inert for downstream projects: their
`.lake/build` is empty at prepare-time (`lake exe cache get` fills only
dependency oleans), so `save_build_baseline` finds nothing to store. It does
real work only when the project IS Mathlib-scale and `cache get` populated the
project root's `.lake/build` (note 09 §3, §4).

Copy-on-write via `mathlib_cache.reflink_tree`; cache-like with simple
eviction. Safe to delete to reclaim space.
"""

from __future__ import annotations

import hashlib
import os
import shutil
from pathlib import Path

from client.mathlib_cache import prepare_workspace_deps, reflink_tree
from client.workspace import LeaseMetadata

BUILD_REL = Path(".lake") / "build"


def store_root() -> Path:
    """Root of the build-baseline store. `$CHOIR_BUILD_STORE` overrides."""
    override = os.environ.get("CHOIR_BUILD_STORE")
    if override:
        return Path(override).expanduser()
    return Path.home() / ".choir" / "build-store"


def build_key(commit: str, toolchain: str) -> str:
    """Stable key for a project-own build baseline = commit + toolchain hash."""
    th = hashlib.sha256(toolchain.encode("utf-8")).hexdigest()[:8]
    return f"{commit[:12]}-{th}"


def _repo_dir(repo: str) -> Path:
    owner, _, name = repo.partition("/")
    return store_root() / owner / name


def baseline_path(repo: str, commit: str, toolchain: str) -> Path:
    """Where a (repo, commit, toolchain) baseline's `.lake/build` lives."""
    return _repo_dir(repo) / build_key(commit, toolchain) / BUILD_REL


def _present(build: Path) -> bool:
    return build.is_dir() and any(build.iterdir())


def restore_build_baseline(
    workspace: Path,
    *,
    repo: str,
    commit: str,
    toolchain: str,
) -> str:
    """COW the project-own build baseline into the workspace if the store has
    one. Called BEFORE deps/cache-get. Calls the module-level ``reflink_tree``
    directly (like ``mathlib_cache``) so tests can monkeypatch it.

    Returns: ``"no-key"`` (no commit/toolchain), ``"present"`` (resume — build
    already there), ``"hit"`` (COW'd from store), ``"miss"`` (no baseline), or
    ``"miss-noreflink"`` (baseline present but reflink unavailable).
    """
    if not commit or not toolchain:
        return "no-key"
    ws_build = workspace / BUILD_REL
    if _present(ws_build):
        return "present"  # resume — leave the existing build alone
    store_build = baseline_path(repo, commit, toolchain)
    if not _present(store_build):
        return "miss"
    if reflink_tree(store_build, ws_build):
        return "hit"
    return "miss-noreflink"


def save_build_baseline(
    workspace: Path,
    *,
    repo: str,
    commit: str,
    toolchain: str,
) -> str:
    """Save the workspace's pristine `.lake/build` as the baseline if non-empty
    and not already stored. Called AFTER deps/cache-get on a fresh workspace.
    Calls the module-level ``reflink_tree`` directly so tests can monkeypatch it.

    Returns: ``"no-key"``, ``"empty"`` (inert downstream path — nothing built),
    ``"present"`` (already stored), ``"saved"``, or ``"saved-nostore"`` (no
    reflink).
    """
    if not commit or not toolchain:
        return "no-key"
    ws_build = workspace / BUILD_REL
    if not _present(ws_build):
        return "empty"
    store_build = baseline_path(repo, commit, toolchain)
    if _present(store_build):
        return "present"
    if reflink_tree(ws_build, store_build):
        return "saved"
    return "saved-nostore"


def evict_build_store(
    repo: str, *, keep_keys: set[str], max_baselines: int = 3
) -> list[str]:
    """Cache-like eviction: keep the live baselines, cap total count, drop the
    oldest of the rest. Returns the keys evicted. Best-effort; never raises."""
    repo_dir = _repo_dir(repo)
    if not repo_dir.is_dir():
        return []
    keys = [p for p in repo_dir.iterdir() if p.is_dir()]
    if len(keys) <= max_baselines:
        return []
    # Oldest first; never evict a live key.
    candidates = sorted(
        (p for p in keys if p.name not in keep_keys),
        key=lambda p: p.stat().st_mtime,
    )
    n_to_drop = len(keys) - max_baselines
    evicted: list[str] = []
    for p in candidates[:n_to_drop]:
        shutil.rmtree(p, ignore_errors=True)
        evicted.append(p.name)
    return evicted


def _read_repo_commit(workspace: Path) -> tuple[str, str]:
    try:
        meta = LeaseMetadata.read(workspace / ".choir-lease.json")
    except (FileNotFoundError, ValueError, KeyError, TypeError):
        return "", ""
    return meta.repo, meta.pinned_commit


def _read_toolchain(workspace: Path) -> str:
    tc = workspace / "lean-toolchain"
    try:
        return tc.read_text(encoding="utf-8").strip()
    except OSError:
        return ""


def prepare_workspace_build_cache(workspace: Path) -> dict[str, str]:
    """Order per note 09 §3: pre-warm `.lake/build` from the store, run the
    dependency prepare (which fetches `.lake/packages` and, for Mathlib-as-
    project, `.lake/build` on a deps miss), then save a pristine `.lake/build`
    baseline. Best-effort; never raises.

    NOTE (note 09 §3, §8): cache-get-skip stays purely dependency-driven, so
    the advancing-fork case (deps HIT but a NEW commit's build baseline MISSES)
    is NOT handled here — that is the deferred warm-store. Fixed-snapshot (one
    commit, many tasks) is safe: after task 1 the build baseline always HITs.
    """
    repo, commit = _read_repo_commit(workspace)
    toolchain = _read_toolchain(workspace)
    restore = (
        restore_build_baseline(workspace, repo=repo, commit=commit, toolchain=toolchain)
        if repo
        else "no-lease"
    )
    deps = prepare_workspace_deps(workspace)
    save = (
        save_build_baseline(workspace, repo=repo, commit=commit, toolchain=toolchain)
        if repo
        else "no-lease"
    )
    return {"deps": deps, "build_restore": restore, "build_save": save}
