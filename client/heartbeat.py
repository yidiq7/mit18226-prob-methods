"""Heartbeat: an edit to the worker's own lease comment (spec D4).

The signal used to be a rolling `choir/heartbeat:YYYY-MM-DD` label, which a
contributor can no longer write. It can always edit *its own* comment, so a
heartbeat is a `heartbeat` lease comment posted once and thereafter edited
in place: `decide_lease` reads freshness off `updated_at`, which an edit
moves, so a lease running for hours costs the thread one comment rather than
one per tick.

The comment id is re-derived from the thread each beat, never cached. The
thread is already the authority, and there is nowhere good to put it anyway:
`claim()` runs before the workspace exists, and threading it through
`LeaseMetadata` would add a field the wire fingerprint hashes
(`lease_conventions`) — a protocol-bump surface. Re-derivation also lets a
beat run from a machine that never held the workspace.

Advisory and best-effort: every failure path returns `False` rather than
raising, because a transient GitHub error must not break a claim or a
backend run.
"""

from __future__ import annotations

from datetime import UTC, datetime

from client import github as gh
from client.lease import lease_comment_body, read_lease_comments
from gate.state.lease_arbiter import (
    DEFAULT_STALE_AFTER_HOURS,
    LeaseComment,
    decide_lease,
    latest_by_login,
)
from gate.state.lease_comment import ACTION_HEARTBEAT


def heartbeat_target(comments: list[LeaseComment], login: str) -> int | None:
    """The comment id to edit for `login`'s next beat, or `None` to post one.

    Two constraints. It must be `login`'s id-highest comment, the only one
    `decide_lease` reads freshness from — hence `latest_by_login` rather than
    a second copy of that rule here; refresh anything earlier and the beat is
    invisible. And it must not be the claim comment, the lease's identity
    anchor, which an edit could mangle and so destroy the lease it meant to
    refresh. So: edit the id-highest comment if it is already a heartbeat,
    else post a new one, which then *becomes* the id-highest — self-healing
    after a re-claim, one comment per beat thereafter.
    """
    latest = latest_by_login(comments).get(login)
    if latest is None or latest.action != ACTION_HEARTBEAT:
        return None
    return latest.id


def heartbeat_comment_body(login: str, now: datetime) -> str:
    """The heartbeat comment body for `login` at `now`.

    The rendered lease block plus one line naming the beat time. That line
    is **outside** the fence, where `parse_lease_comment` cannot see it, so
    refreshing it can never affect how a reader parses the lease — putting
    the timestamp *in* the block would add a field both parties must agree
    on. It also guarantees the PATCH changes something: the lease block
    alone is byte-identical on every beat, and a no-op edit is exactly the
    case where GitHub might reasonably leave `updated_at` alone, silently
    turning a live lease stale.
    """
    block = lease_comment_body(login, ACTION_HEARTBEAT)
    stamp = now.astimezone(UTC).isoformat(timespec="seconds")
    return f"{block}\n_Lease refreshed {stamp}; this comment is edited in place._\n"


def heartbeat(
    repo: str,
    issue: int,
    *,
    login: str | None = None,
    stale_after_hours: int = DEFAULT_STALE_AFTER_HOURS,
    now: datetime | None = None,
) -> bool:
    """Refresh our lease on `repo#issue`. `True` iff a comment was written.

    Reads the thread, confirms we are the holder, then edits our heartbeat
    comment (or posts the first one). The holder check is not ceremony: the
    thread has already been fetched, `decide_lease` is pure, and without it
    a worker whose claim lost — or whose lease went stale and was taken —
    would keep writing beats that every reader ignores.

    Best-effort by contract. `False` means "nothing was written", whether
    because we do not hold the lease or because GitHub refused; callers
    treat it as diagnostic, never as a reason to stop working.
    """
    now = now or datetime.now(UTC)
    try:
        if login is None:
            login = gh.current_user()
        comments = read_lease_comments(repo, issue)
    except gh.GitHubError:
        return False

    holder = decide_lease(
        comments, stale_after_hours=stale_after_hours, now=now
    ).holder
    if holder != login:
        return False

    body = heartbeat_comment_body(login, now)
    target = heartbeat_target(comments, login)
    try:
        if target is None:
            gh.post_comment(repo, issue, body)
        else:
            gh.edit_comment(repo, target, body)
    except gh.GitHubError:
        return False
    return True
