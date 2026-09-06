"""Backend conformance smoke test — `choir backend check` (spec 2026-07-18).

Builds a throwaway git workspace shaped exactly like a real task
workspace (TASK.md, CHOIR.md, .choir-lease.json, .choir-context.md,
topic branch checked out), invokes the configured backend the same way
`choir work` does, and asserts the backend contract:

- exit 0 AND >= 1 new commit on the branch.

No network, no GitHub, no prover toolchain: the synthetic CHOIR.md names
`true` (a no-op) as the build command. A green check means the
*plumbing* conforms — invocation, workspace reading, committing — not
that the backend can prove anything; the gate judges that, on real
tasks. This is the wiring agent's iterate-until-green harness
(docs/agents/BACKENDS.md § "Wiring a specialized prover"), so a mis-wired
backend never burns real task claims.
"""

from __future__ import annotations

import subprocess
from dataclasses import dataclass, field
from datetime import UTC, datetime
from pathlib import Path

from client.backends import get_backend
from client.config import Config, load_config
from client.workspace import LeaseMetadata

CHECK_BRANCH = "choir/0-backend-check"
CHECK_REPO = "choir/backend-check"  # placeholder owner/name; never contacted
TARGET_FILE = "Check.txt"

# The scratch repo needs a commit identity independent of the machine's
# git config (CI runners, fresh machines).
_GIT_ID = [
    "-c",
    "user.name=choir-backend-check",
    "-c",
    "user.email=check@choir.invalid",
]

_CHOIR_MD = """\
# CHOIR.md — workspace contract (conformance check)

Synthetic workspace written by `choir backend check`. No prover
toolchain is present and no network is needed.

- Build command: `true` (a no-op — run it exactly as you would a real
  project's build command).
- Placeholder token: `PLACEHOLDER` (must not remain in Check.txt).
- Deliverable: commits on the current branch. Exit 0 when done.
- Do not push. Do not open a PR.
"""

_PROVE_TASK_MD = """\
# Backend conformance check

This is a synthetic Choir task: it verifies your backend's plumbing,
not its proving ability. Do exactly this:

1. Open `Check.txt` and replace the line `PLACEHOLDER` with `COMPLETE`.
2. Run the build command CHOIR.md names (it is `true`, a no-op).
3. Commit the change to the current branch.

Do not push. Do not open a PR.
"""


def _git(workspace: Path, *args: str) -> str:
    result = subprocess.run(
        ["git", *_GIT_ID, *args],
        cwd=workspace,
        check=True,
        capture_output=True,
        text=True,
    )
    return result.stdout.strip()


def build_check_workspace(root: Path) -> Path:
    """Create the synthetic workspace under `root`; return its path."""
    workspace = root / "workspace"
    workspace.mkdir(parents=True, exist_ok=True)
    _git(workspace, "init", "-q", "-b", "main")
    (workspace / TARGET_FILE).write_text("PLACEHOLDER\n", encoding="utf-8")
    (workspace / "TASK.md").write_text(_PROVE_TASK_MD, encoding="utf-8")
    (workspace / "CHOIR.md").write_text(_CHOIR_MD, encoding="utf-8")
    _git(workspace, "add", "-A")
    _git(workspace, "commit", "-q", "-m", "choir backend check: initial")
    pinned = _git(workspace, "rev-parse", "HEAD")
    _git(workspace, "checkout", "-q", "-b", CHECK_BRANCH)
    meta = LeaseMetadata(
        repo=CHECK_REPO,
        issue=0,
        branch=CHECK_BRANCH,
        pinned_commit=pinned,
        claimed_at=datetime.now(UTC).isoformat(),
        claimed_by="backend-check",
        target_file=TARGET_FILE,
        target_decl="check",
        task_type="prove",
    )
    meta.write(workspace / ".choir-lease.json")
    (workspace / ".choir-context.md").write_text(
        "Synthetic project guidance planted by `choir backend check` so "
        "the CHOIR_CONTEXT path is exercised.\n",
        encoding="utf-8",
    )
    # Mirror a real workspace: metadata files are git-excluded, so a
    # backend running `git add -A` never commits them by accident.
    exclude = workspace / ".git" / "info" / "exclude"
    exclude.parent.mkdir(parents=True, exist_ok=True)
    with exclude.open("a", encoding="utf-8") as f:
        f.write(".choir-lease.json\n.choir-context.md\n")
    return workspace


@dataclass
class CheckResult:
    """Outcome of one conformance run; `failures` name the violated clauses."""

    passed: bool
    failures: list[str] = field(default_factory=list)
    workspace: Path | None = None
    backend_exit: int | None = None


def run_backend_check(
    root: Path,
    *,
    repo: str | None = None,
    config: Config | None = None,
) -> CheckResult:
    """Invoke the configured backend in a synthetic workspace under `root`.

    `repo` resolves the per-project config overlay exactly like
    `choir work`; an explicit `config` skips loading (the CLI passes the
    one it already loaded). Raises `ConfigError`/`ValueError` on a
    malformed config — callers report those, not the contract clauses.
    """
    cfg = config if config is not None else load_config(repo)
    backend = get_backend(cfg.backend.type, command=cfg.backend.command)
    workspace = build_check_workspace(root)
    pinned = LeaseMetadata.read(workspace / ".choir-lease.json").pinned_commit
    task_md = (workspace / "TASK.md").read_text(encoding="utf-8")
    rc = backend.run(workspace=workspace, task_md=task_md)

    failures: list[str] = []
    if rc != 0:
        failures.append(f"backend exited {rc} (contract: exit 0 on success)")
    count = _git(workspace, "rev-list", "--count", f"{pinned}..{CHECK_BRANCH}")
    if count == "0":
        failures.append(
            "no new commits on the branch (prove contract: leave >= 1 commit)"
        )
    head_branch = _git(workspace, "rev-parse", "--abbrev-ref", "HEAD")
    if head_branch != CHECK_BRANCH:
        failures.append(
            f"backend left HEAD on '{head_branch}' (contract: commit to the "
            f"current branch, {CHECK_BRANCH})"
        )
    return CheckResult(
        passed=not failures,
        failures=failures,
        workspace=workspace,
        backend_exit=rc,
    )
