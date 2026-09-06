"""Worker mode: poll-claim-work-submit in a loop.

The headless / cron contributor — leave `choir worker <repo>` running
overnight or under systemd, and it'll keep picking up `choir/available`
tasks, doing the work via the configured backend, and shipping PRs.

This module is the *library-mode* worker; `client.cli.cmd_worker` is a
thin wrapper. Custom harnesses can import `run` directly, or compose
`run_iteration` themselves for finer control.

Tunables match design note 03 (poll loop section) plus standard
exponential-backoff-with-jitter for empty polls. Backoff resets the
moment a claim succeeds — a busy repo never sees the worker idle for
long.
"""

from __future__ import annotations

import contextlib
import os
import random
import sys
import time
from dataclasses import dataclass, field
from datetime import UTC, datetime, timedelta
from enum import Enum
from pathlib import Path

from client import github as gh
from client.backends import get_backend
from client.build_store import prepare_workspace_build_cache
from client.config import ConfigError, load_config
from client.heartbeat import heartbeat
from client.lease import PROJECT_TOML_PATH, ClaimOutcome, claim, lease_holder
from client.scheduling import order_candidates, passes_appetite
from client.status import list_workspaces
from client.submit import SubmitError, submit_at
from client.update import UpdateError, UpdateResult, run_update
from client.work import run_work
from client.workspace import (
    LeaseMetadata,
    WorkspaceError,
    setup_workspace,
    workspace_path,
    workspace_profile,
)
from gate.protocol import PROTOCOL_VERSION, parse_protocol_pin
from gate.state.intake import ParseSuccess, parse_issue_body

# Set on the child side of a worker re-exec (Task 4 / note 13 §6), before
# `os.execv` — so the loop-start "always" auto-update check (which would
# otherwise run again immediately in the freshly re-exec'd process) knows
# to skip itself once. Not consulted by the PROTOCOL_STALE-triggered
# update — a stale pin surviving a re-exec means the update genuinely
# didn't help, and that path already returns on `changed=False`.
CHOIR_WORKER_UPDATED_ENV = "CHOIR_WORKER_UPDATED"

POLL_INTERVAL_BASE = 60.0  # seconds — first poll after an empty result
POLL_INTERVAL_MAX = 600.0  # 10 minutes — backoff ceiling
POLL_BACKOFF_FACTOR = 2.0
POLL_BACKOFF_JITTER = 0.25  # ±25%
RECENTLY_LOST_WINDOW = timedelta(minutes=15)


class IterationResult(Enum):
    """What happened in one iteration of the loop."""

    NO_CANDIDATES = "no_candidates"   # no claimable issues right now
    LOST_RACE = "lost_race"           # another contributor claimed first
    SKIPPED = "skipped"               # claim pre-check rejected (e.g. state changed)
    WORKSPACE_FAILED = "workspace_failed"
    BACKEND_FAILED = "backend_failed"
    NO_COMMITS = "no_commits"         # backend exited with no commits to ship
    SUBMITTED = "submitted"           # full cycle complete
    GITHUB_ERROR = "github_error"     # transient API error; caller backs off
    PROTOCOL_STALE = "protocol_stale"  # repo pin ahead of this client (note 13 §6);
                                        # no claim attempted this iteration


@dataclass
class WorkerState:
    """In-memory state across iterations of the loop.

    `recently_lost` caches issue numbers to skip for `RECENTLY_LOST_WINDOW`
    — despite the name, it holds more than lost races: any claim outcome
    the worker shouldn't immediately re-attempt (a lost race, or a
    persistent pre-check skip) lands here so the loop doesn't spin on it.
    """

    recently_lost: dict[int, datetime] = field(default_factory=dict)
    poll_interval: float = POLL_INTERVAL_BASE
    completed: int = 0


def next_poll_interval(
    current: float,
    *,
    found_claimable: bool,
    jitter_value: float | None = None,
) -> float:
    """Compute the next poll interval.

    On `found_claimable=True`, resets to the base interval. Otherwise
    doubles the current interval up to `POLL_INTERVAL_MAX`. `jitter_value`
    can be injected for tests; default samples from `[-jitter, +jitter]`.
    """
    if found_claimable:
        base = POLL_INTERVAL_BASE
    else:
        base = min(current * POLL_BACKOFF_FACTOR, POLL_INTERVAL_MAX)
    j = (
        jitter_value
        if jitter_value is not None
        else random.uniform(-POLL_BACKOFF_JITTER, POLL_BACKOFF_JITTER)
    )
    out = base * (1 + j)
    # Never sleep less than half the base — even with worst-case jitter.
    return max(POLL_INTERVAL_BASE * 0.5, out)


def is_recently_lost(
    recently_lost: dict[int, datetime],
    issue_number: int,
    now: datetime,
    window: timedelta = RECENTLY_LOST_WINDOW,
) -> bool:
    """Check (and prune-on-expiry) the recently-lost cache.

    Side-effect: if `issue_number` is in the cache but past the window,
    it's removed and the function returns False (the issue is eligible
    again). This keeps the cache from growing unboundedly.
    """
    last = recently_lost.get(issue_number)
    if last is None:
        return False
    if now - last > window:
        del recently_lost[issue_number]
        return False
    return True


def _protocol_gate_stale(repo: str) -> bool:
    """One fetch+parse per iteration (note 13 §6): True iff this client is
    behind the project's pin. Fails open (False) on any read/parse
    failure, per `client.lease._protocol_conflict`'s discipline. Prints
    the stale message itself so `run_iteration` stays a thin check.
    """
    pin_text = gh.get_file_contents(repo, PROJECT_TOML_PATH)
    if pin_text is None:
        return False
    pin = parse_protocol_pin(pin_text)
    if pin <= PROTOCOL_VERSION:
        return False
    print(
        f"protocol stale: project requires protocol {pin}; this client "
        f"speaks {PROTOCOL_VERSION} — run 'choir update'"
    )
    return True


def _reexec() -> None:
    """Replace the current process image in place (module-level seam so
    tests can monkeypatch it — a real call never returns)."""
    os.execv(sys.executable, [sys.executable, *sys.argv])


def _log_updated(result: UpdateResult) -> None:
    print(f"auto-updated {result.old_sha[:7]} -> {result.new_sha[:7]}; restarting")


def _update_and_reexec_if_changed() -> UpdateResult | None:
    """Run `run_update()`; on `changed=True`, log + set the re-exec guard
    env flag + call `_reexec()` (which never returns in real operation).

    Returns the `UpdateResult` when the update ran but left the checkout
    unchanged, or `None` on `UpdateError` (message already printed) or
    after triggering a re-exec.
    """
    try:
        result = run_update()
    except UpdateError as e:
        print(f"auto-update failed: {e}")
        return None
    if result.changed:
        _log_updated(result)
        os.environ[CHOIR_WORKER_UPDATED_ENV] = "1"
        _reexec()
        return None
    return result


def _handle_protocol_stale(auto_update: str) -> None:
    """Auto-update policy for a `PROTOCOL_STALE` iteration (note 13 §6).

    Every path here ends with `run()` returning — there is no case where
    polling should resume without either a successful re-exec (which, in
    real operation, replaces the process before control ever gets back
    here) or the caller exiting with a message. `"never"` prints the
    update instruction. `"required"`/`"always"` run the update: a
    successful update with `changed=True` re-execs; an `UpdateError` or a
    no-op update (`changed=False` — pin ahead but origin has nothing new)
    prints a message instead, so a failing update is never retried in a
    busy loop.
    """
    if auto_update == "never":
        print(
            "protocol stale and worker.auto_update='never' — run "
            "'choir update' and restart the worker"
        )
        return
    result = _update_and_reexec_if_changed()
    if result is not None and not result.changed:
        print(
            "auto-update ran but the checkout didn't change (pin ahead of "
            "origin) — run 'choir update' manually once a fix is available"
        )


def _loop_start_auto_update(repo: str) -> None:
    """`auto_update = "always"`: opportunistically update once before the
    first iteration, when origin moved. Skipped when
    `CHOIR_WORKER_UPDATED` is set — the child side of a just-completed
    re-exec — so a real re-exec doesn't re-trigger itself in a loop.
    Never aborts the worker: an update failure or no-op here just falls
    through to normal polling (this is a freshness nicety, not the hard
    gate — `run_iteration`'s per-iteration check still enforces that).
    """
    if os.environ.get(CHOIR_WORKER_UPDATED_ENV) == "1":
        return
    try:
        cfg = load_config(repo)
    except ConfigError:
        return
    if cfg.worker.auto_update != "always":
        return
    try:
        result = run_update()
    except UpdateError as e:
        print(f"loop-start auto-update check failed: {e}")
        return
    if result.changed:
        _log_updated(result)
        os.environ[CHOIR_WORKER_UPDATED_ENV] = "1"
        _reexec()


def run_iteration(
    repo: str,
    state: WorkerState,
    *,
    now: datetime | None = None,
) -> tuple[IterationResult, int | None]:
    """One iteration: pick a task and try to ship it. Returns (result, issue_no)."""
    now = now or datetime.now(UTC)

    try:
        cfg = load_config(repo)
    except ConfigError as e:
        print(f"config error: {e}")
        return IterationResult.BACKEND_FAILED, None

    # Protocol hard gate, checked once per iteration, before listing
    # issues: a repo pin ahead of this client must never reach a claim
    # attempt (note 13 §6).
    if _protocol_gate_stale(repo):
        return IterationResult.PROTOCOL_STALE, None

    try:
        issues = gh.list_available_issues(repo)
    except gh.GitHubError as e:
        print(f"github error listing tasks: {e}")
        return IterationResult.GITHUB_ERROR, None

    candidates = order_candidates(
        [
            i
            for i in issues
            if not is_recently_lost(state.recently_lost, i.number, now)
            and passes_appetite(
                i.labels,
                accept_types=cfg.worker.accept_types,
                max_difficulty=cfg.worker.max_difficulty,
            )
        ]
    )
    if not candidates:
        return IterationResult.NO_CANDIDATES, None

    target = candidates[0]
    try:
        claim_result = claim(repo, target.number)
    except gh.GitHubError as e:
        print(f"github error claiming #{target.number}: {e}")
        return IterationResult.GITHUB_ERROR, target.number

    if claim_result.outcome == ClaimOutcome.LOST_RACE:
        state.recently_lost[target.number] = now
        return IterationResult.LOST_RACE, target.number
    if claim_result.outcome != ClaimOutcome.WON:
        # SKIPPED (state changed since list) or ERROR — move on. Cache it
        # like a lost race: some skips are persistent, so without this
        # the worker would re-pick and re-skip the same top-priority
        # candidate every iteration and never reach anything else —
        # head-of-line blocking.
        state.recently_lost[target.number] = now
        return IterationResult.SKIPPED, target.number

    # Won the claim. Now: workspace, work, submit.
    try:
        path = _setup_workspace_for_won(repo, target.number)
    except (gh.GitHubError, WorkspaceError) as e:
        print(f"workspace setup failed for #{target.number}: {e}")
        return IterationResult.WORKSPACE_FAILED, target.number

    heartbeat(repo, target.number)

    # Share deps (`.lake/packages`) and, for a Mathlib-scale project, the
    # project's own build oleans (`.lake/build`) from the machine-local stores
    # (COW) instead of a full per-workspace fetch. Best-effort (note 09 §3).
    # lean4-specific; other provers get a store analog with the samples
    # slice (note 12 §9).
    profile = workspace_profile(path)
    if profile.name == "lean4":
        prepare_workspace_build_cache(path)
    else:
        print(f"prover '{profile.name}': dependency caching lands with the samples slice")

    backend = get_backend(cfg.backend.type, command=cfg.backend.command)
    task_md = _read_task_md(path)
    rc = backend.run(workspace=path, task_md=task_md)

    heartbeat(repo, target.number)

    if rc != 0:
        return IterationResult.BACKEND_FAILED, target.number

    try:
        result = submit_at(path)
    except SubmitError as e:
        if "no commits to submit" in str(e):
            return IterationResult.NO_COMMITS, target.number
        print(f"submit failed for #{target.number}: {e}")
        return IterationResult.BACKEND_FAILED, target.number
    except gh.GitHubError as e:
        print(f"github error submitting #{target.number}: {e}")
        return IterationResult.GITHUB_ERROR, target.number

    print(f"✓ #{target.number}: submitted as {result.pr_url}")
    state.completed += 1
    return IterationResult.SUBMITTED, target.number


def run(
    repo: str,
    *,
    max_tasks: int | None = None,
    poll_interval_base: float = POLL_INTERVAL_BASE,
    sleep_fn: callable = time.sleep,
) -> int:
    """Run the worker loop. Returns the number of tasks completed.

    `max_tasks=None` means "run forever" (until Ctrl-C). `sleep_fn` is
    injectable for tests.

    Resilient by design: any unhandled exception from `run_iteration`
    is logged and treated as an error iteration (sleep + backoff +
    continue). The only way for the worker to exit unexpectedly is a
    KeyboardInterrupt (cleanly handled) or `os._exit`. This makes
    `choir worker` safe to leave running overnight: a transient bug
    won't silently kill the loop.
    """
    state = WorkerState(poll_interval=poll_interval_base)
    print(f"choir worker: polling {repo} (max_tasks={max_tasks or 'unlimited'})")

    # auto_update="always": opportunistic freshness check, once, before the
    # first iteration (note 13 §6). Guarded against exec loops by
    # CHOIR_WORKER_UPDATED — see _loop_start_auto_update's docstring.
    _loop_start_auto_update(repo)

    # Finish our own claimed-but-unsubmitted tasks before polling for new
    # ones (design note 06 §5). A killed worker otherwise strands them:
    # they're choir/claimed, not choir/available, so the poll skips them.
    try:
        me = gh.current_user()
    except gh.GitHubError as e:
        print(f"  (skipping resume scan — user lookup failed: {e})")
        me = None
    if me is not None:
        for ws in find_resumable_workspaces(repo, me):
            if max_tasks is not None and state.completed >= max_tasks:
                break
            print(f"resuming in-progress task at {ws}")
            try:
                if run_work(ws) == 0:
                    state.completed += 1
            except Exception as e:  # resume must never kill the loop
                print(f"  resume failed for {ws}: {type(e).__name__}: {e}")

    try:
        while True:
            if max_tasks is not None and state.completed >= max_tasks:
                print(f"✓ completed {state.completed} task(s); stopping")
                return state.completed

            try:
                result, _issue_no = run_iteration(repo, state)
            except Exception as e:
                # An unhandled exception in run_iteration would otherwise
                # kill the worker loop silently. Log and treat as an
                # error iteration so the backoff kicks in.
                print(f"unhandled exception in run_iteration: {type(e).__name__}: {e}")
                result = IterationResult.GITHUB_ERROR

            if result == IterationResult.SUBMITTED:
                # Success — reset interval and immediately poll again.
                state.poll_interval = poll_interval_base
                continue
            if result == IterationResult.LOST_RACE:
                # Lost — try the next candidate immediately, no sleep.
                continue
            if result == IterationResult.PROTOCOL_STALE:
                # run_iteration already printed the stale message. Policy
                # dispatch per worker.auto_update (note 13 §6) — every path
                # either returns from run() or (in real operation) re-execs,
                # so there is nothing left to fall through to.
                try:
                    auto_update = load_config(repo).worker.auto_update
                except ConfigError:
                    auto_update = "required"  # safe fallback; matches the default
                _handle_protocol_stale(auto_update)
                return state.completed

            # No-candidates / errors / failures / no-commits all sleep with
            # backoff.
            state.poll_interval = next_poll_interval(
                state.poll_interval,
                found_claimable=False,
            )
            print(f"  ({result.value}) sleeping {state.poll_interval:.0f}s")
            sleep_fn(state.poll_interval)

    except KeyboardInterrupt:
        print(f"\nInterrupted. Completed {state.completed} task(s).")
        return state.completed


# Lifecycle labels that put a task past the point of resuming: its PR is
# open or merged. A live lease coexists with both — the holder never has to
# release after submitting — so this is checked separately from the lease.
DOWNSTREAM_LABELS = ("choir/in-review", "choir/done", "choir/invalid")


def find_resumable_workspaces(repo: str, me: str) -> list[Path]:
    """Local workspaces for `repo` still leased by `me` and unsubmitted.

    Signal: the issue's lease comments say `me` holds it
    (`gate.state.lease_arbiter`) AND no downstream lifecycle label says the
    work already shipped. Issues that error are skipped.

    Neither half of the pre-D4 signal (`me in issue.assignees` and
    `"choir/claimed" in issue.labels`) survives: a contributor is no longer
    assignable at all, and a freshly claimed task legitimately still reads
    `choir/available` until the orchestrator's next sync — either check
    would strand claimed-but-unsubmitted tasks. The label is consulted only
    for what it *is* authoritative about: the orchestrator's own decision
    that the task has moved on. That check runs first, off the issue read we
    already have, so a shipped task costs no comment-thread fetch.
    """
    out: list[Path] = []
    for entry in list_workspaces():
        if entry.repo != repo:
            continue
        try:
            issue = gh.get_issue(repo, entry.issue)
        except gh.GitHubError:
            continue
        if any(lbl in issue.labels for lbl in DOWNSTREAM_LABELS):
            continue
        try:
            holder, _reason = lease_holder(repo, entry.issue)
        except gh.GitHubError:
            continue
        if holder != me:
            continue
        out.append(entry.workspace_path)
    return out


def _setup_workspace_for_won(repo: str, issue_number: int) -> Path:
    """Re-fetch the canonical record and call setup_workspace.

    Factored out so the worker doesn't duplicate cli._setup_after_claim's
    intake-parse logic.
    """
    issue = gh.get_issue(repo, issue_number)
    parsed = parse_issue_body(issue.body, expected_repo=repo)
    if not isinstance(parsed, ParseSuccess):
        raise WorkspaceError(
            f"issue body no longer parses; can't set up workspace for #{issue_number}"
        )
    self_login = gh.current_user()
    return setup_workspace(
        repo=repo,
        issue=issue_number,
        record=parsed.record,
        body_prose=parsed.body_prose,
        claimed_by=self_login,
    )


def _read_task_md(workspace: Path) -> str:
    task_md_path = workspace / "TASK.md"
    if not task_md_path.is_file():
        return ""
    with contextlib.suppress(OSError):
        return task_md_path.read_text(encoding="utf-8")
    return ""


# Suppress unused-import lint — LeaseMetadata and workspace_path are
# re-exported here for custom-harness callers, even though they're not
# referenced in this module's own code.
_ = LeaseMetadata, workspace_path
