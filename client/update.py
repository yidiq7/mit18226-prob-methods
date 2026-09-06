"""`choir update` — pull the Choir checkout to latest and reinstall deps.

The CLI install layout fact (design note 13 §6): `choir` runs via
`uv run choir` from *inside* a git checkout of Choir itself, so "update"
means updating that checkout in place — `git pull --ff-only` followed by
`uv sync --extra dev` — never a package-manager reinstall. This is also
the routine the headless worker's auto-update (Task 4) calls at loop
boundaries, and the routine `choir claim` offers interactively when the
hard protocol gate refuses a stale client (note 13 §6).

Rails: refuse a dirty checkout, pull fast-forward only (never merge),
never touch anything but the checkout's already-configured `origin`.
Every subprocess call goes through an injectable `runner` so tests never
touch a real repo — mirrors `client._subprocess`'s `CompletedRun` /
`ToolNotFound` conventions.
"""

from __future__ import annotations

from collections.abc import Callable, Sequence
from dataclasses import dataclass
from pathlib import Path

import client
from client._subprocess import CompletedRun, ToolNotFound
from client._subprocess import run as _subprocess_run

Runner = Callable[[Sequence[str], Path], CompletedRun]


class UpdateError(RuntimeError):
    """`choir update` could not proceed. The message is user-facing."""


@dataclass(frozen=True)
class UpdateResult:
    old_sha: str
    new_sha: str
    changed: bool


def choir_checkout_root() -> Path:
    """The git checkout that `uv run choir` is running from.

    Anchored on the `client` package's own file rather than the caller's
    cwd (design note 13 §6, CLI install layout fact). Requires both a
    `.git` entry — a directory for a normal clone, a FILE for a worktree
    (design note 09) — and `gate/protocol.py`, so a stray copy of just the
    `client/` package (no `.git`, or missing sibling packages) fails
    loudly instead of silently pulling nothing or the wrong repo.
    """
    root = Path(client.__file__).resolve().parents[1]
    if not (root / ".git").exists():
        raise UpdateError(
            f"{root} has no .git — this install isn't a Choir git checkout, "
            "so 'choir update' can't pull. Reinstall via join.sh."
        )
    if not (root / "gate" / "protocol.py").exists():
        raise UpdateError(
            f"{root} doesn't look like a full Choir checkout (missing "
            "gate/protocol.py) — 'choir update' can't proceed."
        )
    return root


def _default_runner(cmd: Sequence[str], cwd: Path) -> CompletedRun:
    return _subprocess_run(cmd, cwd=cwd)


def _run(runner: Runner, cmd: Sequence[str], cwd: Path) -> CompletedRun:
    try:
        return runner(cmd, cwd)
    except ToolNotFound as e:
        raise UpdateError(str(e)) from e


def run_update(*, runner: Runner | None = None) -> UpdateResult:
    """Update the Choir checkout in place: pull, then reinstall deps.

    Order (note 13 §6): dirty-tree check first (abort before touching
    anything), capture the old SHA, `git pull --ff-only` (abort on
    non-ff or any failure), capture the new SHA, `uv sync --extra dev`
    (always run — even when the pull was a no-op, since `uv.lock` may
    have moved between the old and new SHA on a prior partial update).
    """
    root = choir_checkout_root()
    run = runner or _default_runner

    status = _run(run, ["git", "status", "--porcelain"], root)
    if not status.ok:
        raise UpdateError(f"git status failed:\n{status.stderr.strip()}")
    if status.stdout.strip():
        raise UpdateError(
            "checkout has uncommitted changes — commit, stash, or discard "
            "them before 'choir update'"
        )

    old_rev = _run(run, ["git", "rev-parse", "HEAD"], root)
    if not old_rev.ok:
        raise UpdateError(f"git rev-parse HEAD failed:\n{old_rev.stderr.strip()}")
    old_sha = old_rev.stdout.strip()

    pull = _run(run, ["git", "pull", "--ff-only"], root)
    if not pull.ok:
        raise UpdateError(f"git pull --ff-only failed:\n{pull.stderr.strip()}")

    new_rev = _run(run, ["git", "rev-parse", "HEAD"], root)
    if not new_rev.ok:
        raise UpdateError(f"git rev-parse HEAD failed:\n{new_rev.stderr.strip()}")
    new_sha = new_rev.stdout.strip()

    sync = _run(run, ["uv", "sync", "--extra", "dev"], root)
    if not sync.ok:
        raise UpdateError(f"uv sync --extra dev failed:\n{sync.stderr.strip()}")

    return UpdateResult(old_sha=old_sha, new_sha=new_sha, changed=old_sha != new_sha)
