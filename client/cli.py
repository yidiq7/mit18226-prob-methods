"""`choir` — the contributor-side CLI.

Subcommands:
  - `choir list <repo>`              — show claimable tasks
  - `choir claim <repo> <issue>`     — claim a task and set up the workspace
  - `choir work [repo] [issue]`      — invoke the configured backend (then auto-submit)
  - `choir submit [repo] [issue]`    — push the branch + open the PR
  - `choir release [repo] [issue]`   — graceful unwind of a claim
  - `choir status`                   — list local workspaces
  - `choir worker <repo>`            — headless loop: poll, claim, work, submit
  - `choir update`                   — pull the Choir checkout + reinstall deps
  - `choir backend check`            — conformance smoke test for the configured backend

Custom harnesses can skip the CLI and import the underlying modules
directly — see `docs/agents/BACKENDS.md` for the library-use pattern.
"""

from __future__ import annotations

import argparse
import shutil
import sys
import tempfile
from argparse import Namespace
from pathlib import Path

from client import github as gh
from client.backend_check import run_backend_check
from client.config import ConfigError, load_config
from client.deps import find_open_deps, format_deps_report
from client.heartbeat import heartbeat
from client.lease import ClaimOutcome, ClaimResult, claim
from client.pins import check_pins, format_pin_report
from client.release import ReleaseError, release_for_issue, release_from_cwd
from client.scheduling import order_candidates
from client.status import format_table, list_workspaces
from client.submit import SubmitError, submit_for_issue, submit_from_cwd
from client.tooling import mathlib_search_advisory
from client.update import UpdateError, run_update
from client.work import run_work
from client.worker import run as worker_run
from client.workspace import (
    WorkspaceError,
    find_workspace_root,
    setup_workspace,
    task_slug,
    workspace_path,
    workspace_profile,
)
from gate.provers import ProverProfile
from gate.state.intake import ParseSuccess, parse_issue_body
from gate.state.labels import Priority, parse_difficulty, parse_priority
from gate.state.task_record import TaskRecord


def cmd_list(args: Namespace) -> int:
    try:
        issues = gh.list_available_issues(args.repo)
    except gh.GitHubError as e:
        print(f"error: {e}", file=sys.stderr)
        return 1

    if not issues:
        print(f"No claimable tasks in {args.repo}.")
        return 0

    print(f"Available tasks in {args.repo}:\n")
    for issue in order_candidates(issues):
        parsed = parse_issue_body(issue.body, expected_repo=args.repo)
        pr = parse_priority(issue.labels)
        d = parse_difficulty(issue.labels)
        tags = ""
        if pr != Priority.NORMAL:
            tags += f"  ({pr.name.lower()} priority)"
        if d is not None:
            tags += f"  [{d.name.lower()}]"
        if isinstance(parsed, ParseSuccess):
            r = parsed.record
            print(f"  #{issue.number:>4}  [{r.type.value}]  {r.target_decl}{tags}")
        else:
            print(f"  #{issue.number:>4}  [INVALID]  {issue.title}{tags}")
    return 0


def cmd_claim(args: Namespace) -> int:
    try:
        result = claim(args.repo, args.issue)
    except gh.GitHubError as e:
        print(f"error: {e}", file=sys.stderr)
        return 1

    if result.outcome == ClaimOutcome.SKIPPED and "protocol" in result.reason:
        return _handle_protocol_stale_skip(result)

    if result.outcome != ClaimOutcome.WON:
        return _print_non_won_outcome(result)

    return _setup_after_claim(args.repo, args.issue)


_UPDATE_HINT = "  Run 'choir update', then re-run the claim."


def _handle_protocol_stale_skip(result: ClaimResult) -> int:
    """A SKIPPED claim whose reason names a protocol mismatch (note 13 §6).

    Interactive (a human at a tty) gets a one-keystroke offer to update
    now; non-tty (a script, a headless invocation) just gets the hint.
    Either way the claim is NOT retried in-process, even right after a
    successful update: this interpreter already loaded the old client
    code, so re-running the claim here would silently keep using it. The
    caller must re-invoke `choir claim`.
    """
    print(f"- Skipped: {result.reason}")

    if not sys.stdin.isatty():
        print(_UPDATE_HINT)
        return 2

    try:
        answer = input("update now? [Y/n] ").strip().lower()
    except (EOFError, KeyboardInterrupt):
        # Ctrl-D / Ctrl-C at the prompt is a decline, not a traceback.
        print()
        print(_UPDATE_HINT)
        return 2
    if answer not in ("", "y", "yes"):
        print(_UPDATE_HINT)
        return 2

    try:
        update_result = run_update()
    except UpdateError as e:
        print(f"error: {e}", file=sys.stderr)
        return 1

    print(f"  updated: {update_result.old_sha[:7]} -> {update_result.new_sha[:7]}")
    print(
        "  This process is still running the old code — re-run the claim "
        "to pick it up."
    )
    return 2


def _setup_after_claim(repo: str, issue_number: int) -> int:
    """Fetch the canonical record, clone the workspace, print next steps."""
    try:
        issue = gh.get_issue(repo, issue_number)
        parsed = parse_issue_body(issue.body, expected_repo=repo)
    except gh.GitHubError as e:
        print(
            f"✓ Claimed #{issue_number}, but failed to re-fetch the issue: {e}",
            file=sys.stderr,
        )
        return 2
    if not isinstance(parsed, ParseSuccess):
        print(
            f"✓ Claimed #{issue_number}, but the issue body no longer parses — "
            "the lease is held but no workspace was set up.",
            file=sys.stderr,
        )
        return 2

    try:
        self_login = gh.current_user()
        path = setup_workspace(
            repo=repo,
            issue=issue_number,
            record=parsed.record,
            body_prose=parsed.body_prose,
            claimed_by=self_login,
        )
    except (WorkspaceError, gh.GitHubError) as e:
        ws_path = workspace_path(repo, issue_number)
        print(
            f"✓ Claimed #{issue_number}, but workspace setup failed: {e}",
            file=sys.stderr,
        )
        print(
            f"  To retry: remove {ws_path}, then claim again. The lease is "
            f"held — 'choir release {repo} {issue_number}' gives it up.",
            file=sys.stderr,
        )
        return 2

    # First beat of the lease — posts the heartbeat comment that every later
    # beat edits in place (spec D4). `login` is passed because we already
    # resolved it above; heartbeat would otherwise look it up again.
    heartbeat(repo, issue_number, login=self_login)

    print(f"✓ Claimed #{issue_number} in {repo}.")
    print(f"  Workspace: {path}")
    print(f"  Branch:    choir/{issue_number}-{task_slug(parsed.record)}")

    # Surface project-pinned tool versions, if any. Advisory-only — a
    # mismatch warns but doesn't block.
    pin_report = format_pin_report(check_pins(path))
    if pin_report:
        print()
        print(pin_report)

    # Advisory: nudge if the project recommends Mathlib search and the
    # contributor hasn't declared a search tool. Soft — never blocks.
    # Only for provers whose profile carries the note-08 nudge (design
    # note 12 §6) — Mathlib search doesn't apply to every prover.
    profile = workspace_profile(path)
    search_advisory = mathlib_search_advisory(path) if profile.search_tooling_note else None
    if search_advisory:
        print()
        print(search_advisory)

    # Advisory: warn if this task's declared dependencies are still
    # open (the orchestrator may have published it early). Soft check —
    # never blocks the claim.
    if parsed.record.deps:
        deps_report = format_deps_report(find_open_deps(repo, parsed.record.deps))
        if deps_report:
            print()
            print(deps_report)

    _print_claim_next_steps(path, parsed.record, profile)
    return 0


def _print_claim_next_steps(
    path: Path, record: TaskRecord, profile: ProverProfile
) -> None:
    """Print the post-claim "Next:" hint.

    Every task type carries a `target_file` (the type-branched review
    task that pointed at a PR instead was removed by spec D1); uses the
    resolved profile's build command instead of a hardcoded lean4
    `lake build`.
    """
    print()
    print("  Next:")
    print(f"    cd {path}")
    build_cmd = " ".join(profile.build_command)
    print(f"    # edit {record.target_file}, run {build_cmd}, commit")
    print("    choir work    # invokes backend + auto-submits on success")


def _print_non_won_outcome(result: ClaimResult) -> int:
    if result.outcome == ClaimOutcome.LOST_RACE:
        print(f"✗ Lost race to @{result.winner}. Try another issue.")
        return 1
    if result.outcome == ClaimOutcome.SKIPPED:
        print(f"- Skipped: {result.reason}")
        return 2
    print(f"! Error: {result.reason}", file=sys.stderr)
    return 3


def cmd_submit(args: Namespace) -> int:
    try:
        if args.repo and args.issue is not None:
            result = submit_for_issue(args.repo, args.issue)
        elif args.repo or args.issue is not None:
            print(
                "error: provide both repo and issue, or neither (to infer from cwd)",
                file=sys.stderr,
            )
            return 1
        else:
            result = submit_from_cwd(Path.cwd())
    except (SubmitError, gh.GitHubError) as e:
        print(f"error: {e}", file=sys.stderr)
        return 1
    print(f"✓ Submitted as {result.pr_url}")
    return 0


def cmd_release(args: Namespace) -> int:
    try:
        if args.repo and args.issue is not None:
            result = release_for_issue(
                args.repo, args.issue, keep_workspace=args.keep_workspace
            )
        elif args.repo or args.issue is not None:
            print(
                "error: provide both repo and issue, or neither (to infer from cwd)",
                file=sys.stderr,
            )
            return 1
        else:
            result = release_from_cwd(
                Path.cwd(), keep_workspace=args.keep_workspace
            )
    except (ReleaseError, gh.GitHubError) as e:
        print(f"error: {e}", file=sys.stderr)
        return 1

    print("✓ Released claim.")
    if not result.workspace_removed:
        if args.keep_workspace:
            print("  (workspace preserved per --keep-workspace)")
    else:
        print("  Local workspace removed.")
    return 0


def cmd_status(args: Namespace) -> int:
    del args  # subparser routes here with no further fields
    entries = list_workspaces()
    sys.stdout.write(format_table(entries))
    return 0


def cmd_worker(args: Namespace) -> int:
    worker_run(args.repo, max_tasks=args.max_tasks)
    return 0


def cmd_update(args: Namespace) -> int:
    del args  # subparser routes here with no further fields
    try:
        result = run_update()
    except UpdateError as e:
        print(f"error: {e}", file=sys.stderr)
        return 1
    if result.changed:
        print(f"updated: {result.old_sha[:7]} -> {result.new_sha[:7]}")
    else:
        print("already up to date")
    return 0


def cmd_backend_check(args: Namespace) -> int:
    try:
        cfg = load_config(args.repo)
    except ConfigError as e:
        print(f"error: {e}", file=sys.stderr)
        return 1
    if cfg.backend.type == "manual":
        print(
            "note: the manual backend makes no commits, so this check cannot "
            "pass — it exists to validate script backends (docs/agents/BACKENDS.md)."
        )
    root = Path(tempfile.mkdtemp(prefix="choir-backend-check-"))
    try:
        result = run_backend_check(root, repo=args.repo, config=cfg)
    except (ValueError, OSError) as e:
        print(f"error: {e}", file=sys.stderr)
        shutil.rmtree(root, ignore_errors=True)
        return 1
    if result.passed:
        print("PASS: backend satisfies the prove contract.")
        shutil.rmtree(root, ignore_errors=True)
        return 0
    for failure in result.failures:
        print(f"FAIL: {failure}")
    print(f"workspace kept for debugging: {result.workspace}")
    return 1


def cmd_work(args: Namespace) -> int:
    # Locate the workspace.
    if args.repo and args.issue is not None:
        path = workspace_path(args.repo, args.issue)
        if not (path / ".choir-lease.json").is_file():
            print(f"error: no workspace at {path}", file=sys.stderr)
            return 1
    elif args.repo or args.issue is not None:
        print(
            "error: provide both repo and issue, or neither (to infer from cwd)",
            file=sys.stderr,
        )
        return 1
    else:
        found = find_workspace_root(Path.cwd())
        if found is None:
            print("error: not in a choir workspace", file=sys.stderr)
            return 1
        path = found

    return run_work(path)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="choir", description="Choir contributor CLI")
    sub = parser.add_subparsers(dest="cmd", required=True)

    list_p = sub.add_parser("list", help="List claimable tasks in a repo")
    list_p.add_argument("repo", help="GitHub repo as owner/name")
    list_p.set_defaults(func=cmd_list)

    claim_p = sub.add_parser(
        "claim", help="Claim an issue and set up the working directory"
    )
    claim_p.add_argument("repo", help="GitHub repo as owner/name")
    claim_p.add_argument("issue", type=int, help="Issue number")
    claim_p.set_defaults(func=cmd_claim)

    submit_p = sub.add_parser(
        "submit", help="Push the branch and open the PR"
    )
    submit_p.add_argument(
        "repo",
        nargs="?",
        help="GitHub repo as owner/name (default: infer from cwd)",
    )
    submit_p.add_argument(
        "issue",
        nargs="?",
        type=int,
        help="Issue number (default: infer from cwd)",
    )
    submit_p.set_defaults(func=cmd_submit)

    release_p = sub.add_parser(
        "release", help="Release a claim (post a release comment, tear down the workspace)"
    )
    release_p.add_argument(
        "repo",
        nargs="?",
        help="GitHub repo as owner/name (default: infer from cwd)",
    )
    release_p.add_argument(
        "issue",
        nargs="?",
        type=int,
        help="Issue number (default: infer from cwd)",
    )
    release_p.add_argument(
        "--keep-workspace",
        action="store_true",
        help="Keep the local workspace directory after release",
    )
    release_p.set_defaults(func=cmd_release)

    status_p = sub.add_parser(
        "status", help="List local workspaces (claims held on this machine)"
    )
    status_p.set_defaults(func=cmd_status)

    work_p = sub.add_parser(
        "work", help="Invoke the configured agent backend in the workspace"
    )
    work_p.add_argument(
        "repo",
        nargs="?",
        help="GitHub repo as owner/name (default: infer from cwd)",
    )
    work_p.add_argument(
        "issue",
        nargs="?",
        type=int,
        help="Issue number (default: infer from cwd)",
    )
    work_p.set_defaults(func=cmd_work)

    worker_p = sub.add_parser(
        "worker",
        help="Headless loop: keep polling and processing tasks until stopped",
    )
    worker_p.add_argument("repo", help="GitHub repo as owner/name")
    worker_p.add_argument(
        "--max-tasks",
        type=int,
        default=None,
        help="Stop after completing N tasks (default: run until Ctrl-C)",
    )
    worker_p.set_defaults(func=cmd_worker)

    update_p = sub.add_parser(
        "update", help="Pull the Choir checkout to latest and reinstall deps"
    )
    update_p.set_defaults(func=cmd_update)

    backend_p = sub.add_parser("backend", help="Backend utilities")
    backend_sub = backend_p.add_subparsers(dest="backend_cmd", required=True)
    check_p = backend_sub.add_parser(
        "check",
        help="Conformance smoke test: invoke the configured backend in a "
        "synthetic scratch workspace (no network, no toolchain) and assert "
        "the contract",
    )
    check_p.add_argument(
        "--type",
        choices=("prove",),
        default="prove",
        help="Which task contract to check (only 'prove' remains since "
        "spec D1 removed the review contract; kept for wrapper-script "
        "compatibility with the 2026-07-18 backend-check spec)",
    )
    check_p.add_argument(
        "--repo",
        default=None,
        help="Resolve the per-project config overlay for this owner/name",
    )
    check_p.set_defaults(func=cmd_backend_check)

    args = parser.parse_args(argv)
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
