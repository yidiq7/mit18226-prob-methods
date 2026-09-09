"""Command-line surface for the orchestrator toolkit.

The library in `orchestrator/` is the reference implementation, and a
Python caller should keep using it. This module exists because an *agent*
does not reach the library the way a program does: it reaches it through a
shell, under a permission system, and a permission rule can only name an
executable and an argument prefix. It cannot say "you may call this one
function", so the only way to grant an orchestrator its own toolkit
without also granting `python -c` — which is arbitrary execution — is to
put a command in front of it.

**Outcomes are in the JSON, never in the exit code.** A merge the gate
refuses is a routine answer to "should this merge?", not a failure of this
tool, so it exits 0 with ``{"merged": false, "reason": ...}``. Reserve
non-zero for "no answer was produced":

    0 — the command ran; read stdout for what happened
    1 — bad arguments
    2 — GitHub / network / auth failure

`merge` cannot override the gate. The override is a separate subcommand,
`merge-override`, so that a permission rule granting `merge` does not also
grant the override — `force` is the overseer's, not the orchestrator's
(`orchestrator/prs.py`, `merge_pr`).
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import Any

from gate.inventory.cli import main as _inventory_main
from gate.jsonio import emit as _emit
from gate.jsonio import plain as _plain
from gate.provers.select import read_prover
from gate.state.task_record import ProjectRef, TaskRecord, TaskType
from orchestrator import joining_prompt as _joining_prompt
from orchestrator import poll as poll_mod
from orchestrator.labels import Difficulty, Priority, set_difficulty, set_priority
from orchestrator.leases import sync_lease_labels
from orchestrator.metrics.cli import main as _metrics_main
from orchestrator.project_config import read_project_config
from orchestrator.prs import (
    PRError,
    blocking_failures,
    close_pr,
    get_pr,
    get_pr_comments,
    get_pr_diff,
    list_open_prs,
    merge_pr,
    missing_required_checks,
    pending_blocking_checks,
    post_pr_comment,
)
from orchestrator.runs import approve_runs_for_sha, pending_approvals
from orchestrator.salvage import classify_failure, create_salvage_task
from orchestrator.tasks import (
    MaintainerError,
    create_task_issue,
    get_task,
    list_choir_tasks,
)


# ----------------------------------------------------------------- reads
def _c_tasks(a: argparse.Namespace) -> int:
    tt = TaskType(a.type) if a.type else None
    return _emit(list_choir_tasks(
        a.repo, state=a.state, task_type=tt, label=a.label, limit=a.limit))


def _c_task(a: argparse.Namespace) -> int:
    return _emit(get_task(a.repo, a.number))


def _c_prs(a: argparse.Namespace) -> int:
    return _emit([_pr_payload(pr, a.prover) for pr in list_open_prs(a.repo, limit=a.limit)])


def _pr_payload(pr: Any, prover: str | None) -> dict[str, Any]:
    """A PR plus the three verdicts the playbook says to read instead of
    `checks_all_green` — computed here so the caller cannot use the wrong
    predicate (`ORCHESTRATOR.md` § Review open PRs)."""
    d = _plain(pr)
    d["blocking_failures"] = blocking_failures(pr, prover=prover)
    d["missing_required_checks"] = missing_required_checks(pr)
    d["pending_blocking_checks"] = pending_blocking_checks(pr, prover=prover)
    d["mergeable_now"] = not (
        d["blocking_failures"] or d["missing_required_checks"] or d["pending_blocking_checks"]
    )
    return d


def _c_pr(a: argparse.Namespace) -> int:
    return _emit(_pr_payload(get_pr(a.repo, a.number), a.prover))


def _c_pr_diff(a: argparse.Namespace) -> int:
    sys.stdout.write(get_pr_diff(a.repo, a.number))
    return 0


def _c_pr_comments(a: argparse.Namespace) -> int:
    return _emit([{"author": au, "body": b} for au, b in get_pr_comments(a.repo, a.number)])


def _c_pending_approvals(a: argparse.Namespace) -> int:
    return _emit(pending_approvals(a.repo, limit=a.limit))


def _c_project_config(a: argparse.Namespace) -> int:
    """Both things the playbook reads once at loop start, in one call."""
    checkout = Path(a.checkout)
    cfg = read_project_config(checkout)
    return _emit({
        "merge_automation": cfg.merge_automation,
        "prover": read_prover(checkout),
    })


def _c_create_task(a: argparse.Namespace) -> int:
    """Publish one task issue. The body round-trips through the gate's
    intake parser, so a task this creates is one a worker can claim."""
    record = TaskRecord(
        choir_task_version=1,
        type=TaskType(a.type),
        target_file=a.target_file,
        target_decl=a.target_decl,
        project_ref=ProjectRef(repo=a.repo, commit=a.commit, toolchain=a.toolchain),
        deps=list(a.dep),
        blueprint_ref=a.blueprint_ref,
    )
    number = create_task_issue(
        a.repo, task=record, title=a.title, prose=a.prose,
        extra_labels=tuple(a.label),
    )
    return _emit({"created": True, "number": number, "title": a.title})


# ------------------------------------------------------------- mutations
def _merge(a: argparse.Namespace, force: str | None) -> int:
    """Shared body for `merge` and `merge-override`.

    Resolve the PR first. A PR that cannot be read is infrastructure
    failing (exit 2); only once it reads can a PRError be what the gate
    decided, which is an answer and exits 0 — see the module docstring.
    """
    get_pr(a.repo, a.number)          # raises PRError -> caught in main() -> exit 2
    try:
        merge_pr(a.repo, a.number, method=a.method,
                 delete_branch=not a.keep_branch, prover=a.prover, force=force)
    except PRError as e:
        return _emit({"merged": False, "number": a.number, "refused": str(e)})
    out = {"merged": True, "number": a.number, "method": a.method}
    if force is not None:
        out["overridden"] = True
        out["reason"] = force
    return _emit(out)


def _c_merge(a: argparse.Namespace) -> int:
    return _merge(a, None)


def _c_merge_override(a: argparse.Namespace) -> int:
    return _merge(a, a.reason)


def _c_poll(a: argparse.Namespace) -> int:
    """The loop clock, as a subcommand.

    Delegates to `orchestrator.poll`, which stays runnable on its own.
    Reached this way `--repo` is always supplied, so the poller never has
    to guess which project it is watching — the per-project config is keyed
    by repo, and without one it can only fall back to the legacy
    single-project file.
    """
    argv = ["--repo", a.repo]
    if a.prover:
        argv += ["--prover", a.prover]
    if a.interval is not None:
        argv += ["--interval", str(a.interval)]
    if a.max_wait is not None:
        argv += ["--max-wait", str(a.max_wait)]
    if a.once:
        argv.append("--once")
    return poll_mod.main(argv)


# Three tools the loop uses that keep their own parsers. They are forwarded
# verbatim rather than re-declared here, so each stays the single definition
# of its own interface — and `python -m orchestrator.metrics`,
# `python -m orchestrator.joining_prompt` and `python -m gate.inventory` all
# still work. `gate.inventory` lives under `gate` because the scanning logic
# does; its CLI is an orchestrator tool, which is why it belongs in this table.
def _c_metrics(a: argparse.Namespace) -> int:
    return _metrics_main(a.args)


def _c_joining_prompt(a: argparse.Namespace) -> int:
    return _joining_prompt.main(a.args)


def _c_inventory(a: argparse.Namespace) -> int:
    return _inventory_main(a.args)


def _c_classify(a: argparse.Namespace) -> int:
    """TRUST or NEAR_MISS for a set of failed checks.

    Salvage always reads strict, so this takes no `--prover`: a check that
    is advisory for one prover must not quietly downgrade a trust failure.
    """
    return _emit({"failed_checks": a.failed_check,
                  "failure_class": classify_failure(a.failed_check)})


def _c_salvage(a: argparse.Namespace) -> int:
    """Open a salvage task from a near-miss PR, carrying the original's
    record forward — fetched here so the caller need not restate it."""
    original = get_task(a.repo, a.issue).record
    if original is None:
        print(f"error: issue #{a.issue} has no parsable task record", file=sys.stderr)
        return 1
    number = create_salvage_task(
        a.repo, original=original, original_issue=a.issue, pr_number=a.pr,
        pr_head_sha=a.head_sha, failed_checks=a.failed_check, detail=a.detail,
    )
    return _emit({"created": True, "number": number, "salvages_issue": a.issue})


def _c_close(a: argparse.Namespace) -> int:
    close_pr(a.repo, a.number, comment=a.comment)
    return _emit({"closed": True, "number": a.number})


def _c_comment(a: argparse.Namespace) -> int:
    post_pr_comment(a.repo, a.number, a.body)
    return _emit({"commented": True, "number": a.number})


def _c_approve_runs(a: argparse.Namespace) -> int:
    return _emit(approve_runs_for_sha(a.repo, a.sha))


def _c_set_priority(a: argparse.Namespace) -> int:
    set_priority(a.repo, a.number, Priority[a.value.upper()])
    return _emit({"number": a.number, "priority": a.value.upper()})


def _c_set_difficulty(a: argparse.Namespace) -> int:
    set_difficulty(a.repo, a.number, Difficulty[a.value.upper()])
    return _emit({"number": a.number, "difficulty": a.value.upper()})


def _c_sync_leases(a: argparse.Namespace) -> int:
    """Labels are a projection of the lease comments; this reconciles them.

    The library takes the (number, labels) pairs from the caller. Reading
    them here is the whole point of the subcommand — an agent should not
    have to assemble that list in shell to call one function.
    """
    tasks = list_choir_tasks(a.repo, state="open", limit=a.limit)
    pairs = [(t.number, list(t.labels)) for t in tasks]
    changes = sync_lease_labels(
        a.repo, pairs, stale_after_hours=a.stale_after_hours, apply=not a.dry_run)
    return _emit({"scanned": len(pairs), "dry_run": a.dry_run, "changes": changes})


# Subcommands that name their own target instead of the project repo: the
# passthroughs carry it in their own arguments, `inventory` and
# `project-config` take a local checkout, and `classify` is a pure function
# over check names.
_NO_REPO = frozenset(
    {"metrics", "joining-prompt", "inventory", "project-config", "classify"}
)


def _build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="choir orch",
        description="Orchestrator toolkit as commands. Outcomes are in the JSON, "
                    "not the exit code: 0 = answered, 1 = bad args, 2 = GitHub failed.",
    )
    p.add_argument("--repo", default=None, help="owner/name of the project repo")
    p.add_argument("--prover", default=None,
                   help="lean4 | isabelle | rocq. Omit and every check is read in its "
                        "strict class, so an advisory red (statement-equiv on lean4) "
                        "reads as blocking.")
    sub = p.add_subparsers(dest="cmd", required=True)

    def add(name: str, fn, help_: str):
        s = sub.add_parser(name, help=help_)
        s.set_defaults(fn=fn)
        return s

    s = add("tasks", _c_tasks, "Choir task issues")
    s.add_argument("--state", choices=["open", "closed", "all"], default="all")
    s.add_argument("--type", choices=["prove", "golf", "index"], default=None)
    s.add_argument("--label", default=None)
    s.add_argument("--limit", type=int, default=200)

    s = add("task", _c_task, "one task issue, parsed")
    s.add_argument("number", type=int)

    s = add("prs", _c_prs, "open PRs, each with its three check verdicts")
    s.add_argument("--limit", type=int, default=100)

    s = add("pr", _c_pr, "one PR, with its three check verdicts")
    s.add_argument("number", type=int)

    s = add("pr-diff", _c_pr_diff, "the PR diff, as text")
    s.add_argument("number", type=int)

    s = add("pr-comments", _c_pr_comments, "(author, body) per comment")
    s.add_argument("number", type=int)

    s = add("pending-approvals", _c_pending_approvals, "fork runs GitHub is holding")
    s.add_argument("--limit", type=int, default=100)

    s = add("project-config", _c_project_config,
            "automation level + prover, from a local checkout")
    s.add_argument("checkout", help="path to the local project checkout")

    s = add("poll", _c_poll,
            "block until the repo's Choir state changes, then exit")
    s.add_argument("--interval", type=int, default=None,
                   help="seconds between checks (default from local config, else 600)")
    s.add_argument("--max-wait", type=int, default=None,
                   help="give up after this many seconds (default 3600)")
    s.add_argument("--once", action="store_true",
                   help="print the current snapshot and exit")

    _add_write_commands(add)
    return p


def _add_write_commands(add) -> None:  # type: ignore[no-untyped-def]
    """The mutating half. `merge` and `merge-override` are separate
    subcommands so that a permission rule granting one does not grant the
    other — see the module docstring."""
    s = add("merge", _c_merge, "merge a PR — refuses unless the gate is green")
    s.add_argument("number", type=int)
    s.add_argument("--method", choices=["squash", "merge", "rebase"], default="squash")
    s.add_argument("--keep-branch", action="store_true")

    s = add("merge-override", _c_merge_override,
            "OVERSEER ONLY: merge past a red gate, with an attributable reason")
    s.add_argument("number", type=int)
    s.add_argument("--reason", required=True,
                   help="why the override is justified; posted to the PR before merging")
    s.add_argument("--method", choices=["squash", "merge", "rebase"], default="squash")
    s.add_argument("--keep-branch", action="store_true")

    s = add("create-task", _c_create_task, "publish one task issue")
    s.add_argument("--title", required=True)
    s.add_argument("--target-file", required=True)
    s.add_argument("--target-decl", required=True)
    s.add_argument("--commit", required=True, help="project_ref commit the task pins")
    s.add_argument("--toolchain", required=True, help="project_ref toolchain")
    s.add_argument("--type", choices=["prove", "golf", "index"], default="prove")
    s.add_argument("--dep", type=int, action="append", default=[],
                   help="issue number this task was decomposed from (repeatable)")
    s.add_argument("--blueprint-ref", default=None, help="the plan node this fills")
    s.add_argument("--prose", default="", help="statement context, hints, references")
    s.add_argument("--label", action="append", default=[], help="extra label (repeatable)")

    for name, fn, help_ in (
        ("metrics", _c_metrics, "per-task lifecycle data (forwards to orchestrator.metrics)"),
        ("joining-prompt", _c_joining_prompt, "print the contributor joining prompt"),
        ("inventory", _c_inventory, "every axiom + sorry in a checkout, with locations"),
    ):
        s = add(name, fn, help_)
        s.add_argument("args", nargs=argparse.REMAINDER,
                       help="arguments passed through unchanged")

    s = add("classify", _c_classify, "TRUST or NEAR_MISS for a set of failed checks")
    s.add_argument("--failed-check", action="append", default=[], required=True,
                   help="name of a failed check (repeatable)")

    s = add("salvage", _c_salvage, "open a salvage task from a near-miss PR")
    s.add_argument("--issue", type=int, required=True, help="the original task issue")
    s.add_argument("--pr", type=int, required=True)
    s.add_argument("--head-sha", required=True)
    s.add_argument("--failed-check", action="append", default=[], required=True)
    s.add_argument("--detail", default="")

    s = add("close", _c_close, "close a PR without merging")
    s.add_argument("number", type=int)
    s.add_argument("--comment", default=None)

    s = add("comment", _c_comment, "post a PR comment")
    s.add_argument("number", type=int)
    s.add_argument("--body", required=True)

    s = add("approve-runs", _c_approve_runs, "approve held fork runs at a head SHA")
    s.add_argument("sha")

    s = add("set-priority", _c_set_priority, "set choir/priority:*")
    s.add_argument("number", type=int)
    s.add_argument("value", choices=["low", "normal", "high"])

    s = add("set-difficulty", _c_set_difficulty, "set choir/difficulty:*")
    s.add_argument("number", type=int)
    s.add_argument("value", choices=["easy", "medium", "hard"])

    s = add("sync-leases", _c_sync_leases, "reconcile lease labels with lease comments")
    s.add_argument("--stale-after-hours", type=int, default=24)
    s.add_argument("--dry-run", action="store_true")
    s.add_argument("--limit", type=int, default=200)


def main(argv: list[str] | None = None) -> int:
    parser = _build_parser()
    a = parser.parse_args(argv)
    if a.repo is None and a.cmd not in _NO_REPO:
        parser.error(f"--repo is required for '{a.cmd}'")
    try:
        return a.fn(a)
    except (PRError, MaintainerError) as e:
        print(f"error: {e}", file=sys.stderr)
        return 2
    except KeyError as e:
        print(f"error: bad value {e}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
