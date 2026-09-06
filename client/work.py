"""Shared 'run the backend in a prepared workspace and submit' path.

Used by `choir work` (cli) and the worker loop's resume scan. Heartbeats
around the backend invocation; auto-submits on success; treats
nothing-to-ship as success (the Manual backend lands there).
"""
from __future__ import annotations

import sys
from pathlib import Path

from client import github as gh
from client.backends import get_backend
from client.build_store import prepare_workspace_build_cache
from client.config import ConfigError, load_config
from client.heartbeat import heartbeat
from client.submit import SubmitError, submit_at
from client.workspace import LeaseMetadata, workspace_profile


def run_work(workspace: Path) -> int:
    """Invoke the configured backend in `workspace`, then auto-submit."""
    try:
        meta: LeaseMetadata | None = LeaseMetadata.read(workspace / ".choir-lease.json")
    except (FileNotFoundError, KeyError, TypeError, ValueError):
        meta = None  # heartbeats are advisory; run the backend regardless

    # Resolve the backend with the lease's repo so a per-project config.json
    # override applies; falls back to the global config when there's no lease.
    try:
        cfg = load_config(meta.repo if meta is not None else None)
    except ConfigError as e:
        print(f"error: {e}", file=sys.stderr)
        return 1

    if meta is not None:
        heartbeat(meta.repo, meta.issue)

    # Populate the workspace's deps (`.lake/packages`) and, for a Mathlib-scale
    # project, its own build oleans (`.lake/build`) from the machine-local
    # shared stores via copy-on-write instead of a full per-workspace fetch — so
    # N tasks on one machine cost ~one copy, not N. Best-effort; the backend's
    # own `lake exe cache get` still covers any miss (note 09 §3). This is a
    # lean4-specific dependency-caching mechanism (`.lake/`); other provers
    # get their own store analogs with the samples slice (note 12 §9).
    profile = workspace_profile(workspace)
    if profile.name == "lean4":
        prepare_workspace_build_cache(workspace)
    else:
        print(f"prover '{profile.name}': dependency caching lands with the samples slice")

    backend = get_backend(cfg.backend.type, command=cfg.backend.command)
    task_md_path = workspace / "TASK.md"
    task_md = task_md_path.read_text(encoding="utf-8") if task_md_path.is_file() else ""
    rc = backend.run(workspace=workspace, task_md=task_md)

    if meta is not None:
        heartbeat(meta.repo, meta.issue)

    if rc != 0:
        return rc
    return _auto_submit(workspace)


def _auto_submit(workspace: Path) -> int:
    try:
        result = submit_at(workspace)
    except SubmitError as e:
        if "no commits to submit" in str(e):
            return 0  # nothing to ship — not an error
        print(f"error: {e}", file=sys.stderr)
        return 1
    except gh.GitHubError as e:
        print(f"error: {e}", file=sys.stderr)
        return 1
    verb = "Reused existing PR" if result.reused_existing_pr else "Submitted as"
    print(f"✓ {verb}: {result.pr_url}")
    return 0
