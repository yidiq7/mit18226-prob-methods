"""Claim-ordering and appetite filtering for the worker loop (note 11 §4).

Ordering: priority descending, then age ascending — issue number is
the age proxy (GitHub numbers are monotonic). Difficulty is a FILTER,
never an ordering key: a high-priority hard task must not lose to a
low-priority easy one for a worker able to take both.

Every filter fails open on absent labels: no type label / no
difficulty label / unknown cap values all pass. Absence of a label
must never make a task unclaimable.
"""

from __future__ import annotations

from collections.abc import Iterable

from client.github import Issue
from gate.state.labels import Difficulty, parse_difficulty, parse_priority

TYPE_LABEL_PREFIX = "choir/type:"

_DIFFICULTY_CAPS = {
    "easy": Difficulty.EASY,
    "medium": Difficulty.MEDIUM,
    "hard": Difficulty.HARD,
}


def task_type_label(labels: Iterable[str]) -> str | None:
    """The task type from `choir/type:*`, or None when unlabeled."""
    for lbl in labels:
        if lbl.startswith(TYPE_LABEL_PREFIX):
            return lbl[len(TYPE_LABEL_PREFIX):]
    return None


def passes_appetite(
    labels: list[str],
    *,
    accept_types: list[str] | None,
    max_difficulty: str | None,
) -> bool:
    """Contributor appetite check (`worker` section of config.json)."""
    if accept_types is not None:
        t = task_type_label(labels)
        if t is not None and t not in accept_types:
            return False
    if max_difficulty is not None:
        cap = _DIFFICULTY_CAPS.get(max_difficulty)
        d = parse_difficulty(labels)
        if cap is not None and d is not None and d > cap:
            return False
    return True


def order_candidates(issues: list[Issue]) -> list[Issue]:
    """Priority desc, then issue number asc (age proxy)."""
    return sorted(issues, key=lambda i: (-int(parse_priority(i.labels)), i.number))
