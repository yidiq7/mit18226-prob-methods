"""Sorry-delta audit (Phase 3).

Fails PRs that *increase* the number of `sorry`s in any changed `.lean`
file. Closing sorries (the normal work product) passes; smuggling new
ones in — including into declarations the task didn't ask about — does
not.

Why this audit exists: `lake build` treats `sorry` as a *warning*, not
an error, so the clean-room rebuild alone would merge a "proof" that is
still sorry-shaped. Per the 2026-05-07 decision, final-submission sorry
blocks merge. (The `partial_progress` return state — where a checkpoint
with remaining sorries is explicitly accepted and replanned around — is
a v0.5 feature; when it lands, it will be an explicit task-level
escape hatch, not a weakening of this audit.)

Counting uses the inventory's comment-stripped scan, unlike the other
pattern audits: a comment that merely *mentions* sorry must not fail a
contributor's PR. Stripping comments is strictly more accurate here —
commented-out code doesn't elaborate, so it can't hide a real sorry.

Like the other v0 audits this is per-file and regex-based; `sorryAx`
spelled directly and metaprogramming tricks are out of scope (design
note 05's axiom-trace workflow is the kernel-level answer).
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum

from gate.inventory.scan import SorryItem, scan_text
from gate.provers.base import ProverProfile
from gate.provers.lean4 import LEAN4


class Verdict(Enum):
    CLEAN = "clean"
    INTRODUCED = "introduced"


@dataclass(frozen=True)
class Finding:
    """Sorry counts for one file where head > base."""

    base_count: int
    head_count: int
    head_sorries: tuple[SorryItem, ...]

    @property
    def delta(self) -> int:
        return self.head_count - self.base_count


def count_sorries(
    file_contents: str,
    file_path: str = "<file>",
    *,
    profile: ProverProfile = LEAN4,
) -> list[SorryItem]:
    """All placeholder occurrences in the file, comments stripped.

    `profile` selects which tokens count as placeholders (`sorry` for
    lean4; `sorry`/`oops` for isabelle; `Admitted`/`admit`/`Abort` for
    rocq) and the comment syntax used to strip comments first. Defaults
    to lean4 so existing callers are unchanged.
    """
    _axioms, sorries = scan_text(file_contents, file_path, profile=profile)
    return sorries


def compare(
    base_contents: str,
    head_contents: str,
    *,
    file_path: str = "<file>",
    profile: ProverProfile = LEAN4,
) -> tuple[Verdict, Finding | None]:
    """Compare placeholder counts; INTRODUCED iff head has more than base.

    Reducing or holding the count passes — a PR editing a file that
    already carries placeholders (e.g., progress on one of several) is
    fine as long as it doesn't add new ones.
    """
    base = count_sorries(base_contents, file_path, profile=profile)
    head = count_sorries(head_contents, file_path, profile=profile)
    if len(head) > len(base):
        return Verdict.INTRODUCED, Finding(
            base_count=len(base),
            head_count=len(head),
            head_sorries=tuple(head),
        )
    return Verdict.CLEAN, None


def format_finding(finding: Finding) -> str:
    """Render one file's finding for status-check output."""
    lines = [
        f"sorries: base {finding.base_count} → head {finding.head_count} "
        f"(**+{finding.delta}**)",
        "",
        "| declaration | line |",
        "|---|---|",
    ]
    for s in finding.head_sorries:
        decl = f"`{s.decl}`" if s.decl else "(no enclosing decl)"
        lines.append(f"| {decl} | {s.line} |")
    return "\n".join(lines)
