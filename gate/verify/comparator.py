"""Comparator workspace/config/verdict logic (design note 14).

`leanprover/comparator` is the Lean FRO's kernel-level judge: given a
trusted Challenge module and an untrusted Solution module in one Lake
workspace, it certifies that the solution proves *exactly* the
challenge's statement, uses only permitted axioms, and replays through
the kernel. Choir maps a PR onto that model per note 14 §4:

- Challenge side = the **base SHA** tree, module-prefixed under
  `ChoirBase/` so it can coexist with the head tree in one workspace.
  Renaming modules never renames *declarations* (Lean decl names come
  from namespaces, not file paths), which is what keeps the comparison
  sound: both environments hold the target under the same name,
  elaborated against base definitions on one side and head definitions
  on the other.
- Solution side = the head tree verbatim.
- Generated roots (`Challenge.lean`, `Solution.lean`, `ChoirBase.lean`)
  and three appended `[[lean_lib]]` blocks make both sides buildable.

This module is the pure half — text generation, config mapping, verdict
classification — fully unit-testable without git, Lake, or the
comparator binary. The side-effectful half (git materialization and
invocation) lives in `comparator_cli.py`.
"""

from __future__ import annotations

import json
import re
import tomllib
from enum import Enum

from gate.verify.config import AxiomPolicy, SorryPolicy, VerifyConfig

CORE_PERMITTED_AXIOMS: tuple[str, ...] = (
    "propext",
    "Quot.sound",
    "Classical.choice",
)
"""Mathlib's standard trio — always permitted (note 14 §5)."""

SORRY_AXIOM = "sorryAx"
"""Appended under sorry policy `report`: comparator then degrades to
"right statement, kernel-consistent modulo sorry" for checkpoint PRs."""

COMPARATOR_MIN_TOOLCHAIN: tuple[int, int] = (4, 27)
"""Earliest upstream comparator tag is v4.27.0 — older toolchains have
no comparator build at all and the audit is not applicable."""

CHALLENGE_PREFIX = "ChoirBase"
"""Module prefix for the base-SHA tree inside the generated workspace."""

RESERVED_LIB_NAMES: frozenset[str] = frozenset({"Challenge", "Solution", CHALLENGE_PREFIX})
"""Lib names the generator adds; a project already using one collides."""


class ComparatorConfigError(RuntimeError):
    """Workspace generation cannot proceed (bad lakefile, name collision)."""


class Outcome(Enum):
    """Classification of a comparator run (note 14 §6)."""

    MATCH = "match"
    STATEMENT_MISMATCH = "statement-mismatch"
    ILLEGAL_AXIOM = "illegal-axiom"
    MISSING_CONSTANT = "missing-constant"
    TOOL_ERROR = "tool-error"
    SOLUTION_BUILD_FAILED = "solution-build-failed"
    SANDBOX_UNAVAILABLE = "sandbox-unavailable"


# ---------------------------------------------------------------------------
# toolchain floor
# ---------------------------------------------------------------------------

_VERSION_RE = re.compile(r"^v?(\d+)\.(\d+)(?:[.\-]|$)")


def parse_toolchain_version(text: str) -> tuple[int, int] | None:
    """Extract `(major, minor)` from a `lean-toolchain` pin.

    Accepts `leanprover/lean4:v4.31.0`, `v4.33.0-rc1`, and bare
    `4.31.0`. Returns None for anything it can't read (nightlies,
    garbage) — the caller treats that as "can't tell", not an error.
    """
    tail = text.strip().rsplit(":", 1)[-1]
    m = _VERSION_RE.match(tail)
    if m is None:
        return None
    return (int(m.group(1)), int(m.group(2)))


def toolchain_supported(text: str) -> bool | None:
    """Is the pinned toolchain at or above the comparator floor?

    None when the pin is unparseable (distinct from a definite no).
    """
    version = parse_toolchain_version(text)
    if version is None:
        return None
    return version >= COMPARATOR_MIN_TOOLCHAIN


# ---------------------------------------------------------------------------
# module names + import rewriting
# ---------------------------------------------------------------------------


def module_of_path(path: str) -> str:
    """`A/B.lean` → `A.B`."""
    return path.removesuffix(".lean").replace("/", ".")


def base_module_set(paths: list[str]) -> frozenset[str]:
    """Module names of every base-tree `.lean` file — the rewrite domain."""
    return frozenset(module_of_path(p) for p in paths)


_IMPORT_RE = re.compile(r"^(\s*)import\s+([\w.«»]+)(.*)$")


def rewrite_imports(text: str, modules: frozenset[str]) -> str:
    """Prefix internal imports with `ChoirBase.`; leave everything else.

    Only whole-module matches on `import` lines are rewritten —
    `import Mathlib.Tactic` and `import Projection` (a non-internal
    name sharing a prefix with an internal one) pass through untouched.
    """
    out: list[str] = []
    for line in text.splitlines(keepends=True):
        stripped = line.rstrip("\n")
        m = _IMPORT_RE.match(stripped)
        if m is not None and m.group(2) in modules:
            newline = "\n" if line.endswith("\n") else ""
            out.append(
                f"{m.group(1)}import {CHALLENGE_PREFIX}.{m.group(2)}{m.group(3)}{newline}"
            )
        else:
            out.append(line)
    return "".join(out)


# ---------------------------------------------------------------------------
# lakefile handling
# ---------------------------------------------------------------------------


def lean_lib_names(lakefile_text: str) -> list[str]:
    """`name` of every `[[lean_lib]]` in a `lakefile.toml` text."""
    try:
        data = tomllib.loads(lakefile_text)
    except tomllib.TOMLDecodeError as e:
        raise ComparatorConfigError(f"malformed lakefile.toml — {e}") from e
    libs = data.get("lean_lib", [])
    if not isinstance(libs, list):
        raise ComparatorConfigError("lakefile.toml lean_lib must be an array of tables")
    return [lib["name"] for lib in libs if isinstance(lib, dict) and "name" in lib]


def workspace_lakefile(base_lakefile_text: str) -> str:
    """Base lakefile text + the three generated `[[lean_lib]]` blocks.

    Appending array-of-table blocks at EOF is valid TOML as long as no
    other top-level table follows — the base text is preserved verbatim
    as the prefix, so parseability of the result is covered by tests.
    """
    existing = lean_lib_names(base_lakefile_text)
    collisions = RESERVED_LIB_NAMES.intersection(existing)
    if collisions:
        raise ComparatorConfigError(
            f"project lakefile already defines reserved lib(s): {sorted(collisions)}"
        )
    blocks = "".join(
        f'\n[[lean_lib]]\nname = "{lib}"\n'
        for lib in ("Challenge", "Solution", CHALLENGE_PREFIX)
    )
    sep = "" if base_lakefile_text.endswith("\n") else "\n"
    return (
        base_lakefile_text
        + sep
        + "\n# --- appended by gate.verify.comparator (design note 14) ---"
        + blocks
    )


# ---------------------------------------------------------------------------
# generated root modules
# ---------------------------------------------------------------------------


def _ordered_modules(root_libs: list[str], target_module: str) -> list[str]:
    mods = list(root_libs)
    if target_module not in mods:
        mods.append(target_module)
    return mods


def challenge_root(root_libs: list[str], target_module: str) -> str:
    """`Challenge.lean` — imports the *prefixed* base-tree modules."""
    return "".join(
        f"import {CHALLENGE_PREFIX}.{m}\n"
        for m in _ordered_modules(root_libs, target_module)
    )


def solution_root(root_libs: list[str], target_module: str) -> str:
    """`Solution.lean` — imports the head-tree modules verbatim."""
    return "".join(
        f"import {m}\n" for m in _ordered_modules(root_libs, target_module)
    )


def choirbase_root(root_libs: list[str]) -> str:
    """`ChoirBase.lean` — a buildable root for the prefixed lib."""
    return "".join(f"import {CHALLENGE_PREFIX}.{m}\n" for m in root_libs)


# ---------------------------------------------------------------------------
# comparator config
# ---------------------------------------------------------------------------


def permitted_axioms(config: VerifyConfig) -> tuple[str, ...]:
    """Translate base-SHA `.choir/verify.toml` policy to a whitelist.

    Core three always (Choir's introduction-based policies presume
    them); `whitelist` mode unions `allowed_axioms`; sorry policy
    `report` appends `sorryAx` (note 14 §5). The translation is honest
    but not exact — see the note for the net_zero false-reject caveat.
    """
    permitted = list(CORE_PERMITTED_AXIOMS)
    if config.axiom_honesty.policy is AxiomPolicy.WHITELIST:
        for name in config.axiom_honesty.allowed_axioms:
            if name not in permitted:
                permitted.append(name)
    if config.sorry_delta.policy is SorryPolicy.REPORT:
        permitted.append(SORRY_AXIOM)
    return tuple(permitted)


def comparator_config_json(target_decl: str, permitted: tuple[str, ...]) -> str:
    """The workspace's `config.json` for the comparator binary."""
    return (
        json.dumps(
            {
                "challenge_module": "Challenge",
                "solution_module": "Solution",
                "theorem_names": [target_decl],
                "permitted_axioms": list(permitted),
                "enable_nanoda": False,
            },
            indent=2,
        )
        + "\n"
    )


# ---------------------------------------------------------------------------
# verdict classification
# ---------------------------------------------------------------------------

_FAILURE_PATTERNS: tuple[tuple[str, Outcome], ...] = (
    # Genuine verdicts — must stay ahead of the two infra/build patterns
    # below so a real verdict is never masked by incidental build chatter
    # that happens to precede it in the transcript (a failed rebuild can
    # print "error: build failed" and *still* carry a verdict line).
    ("theorem statement do not match", Outcome.STATEMENT_MISMATCH),
    ("Illegal axiom detected", Outcome.ILLEGAL_AXIOM),
    ("Const not found in challenge", Outcome.MISSING_CONSTANT),
    ("Const not found in solution", Outcome.MISSING_CONSTANT),
    ("Const does not match between challenge and target", Outcome.MISSING_CONSTANT),
    # Infrastructure, not the worker's code. Comparator has no unsandboxed
    # mode: with COMPARATOR_LANDRUN unset it PATH-looks-up the literal string
    # "landrun" and dies, so this is also what an unset env var looks like.
    ("could not execute external process 'landrun'", Outcome.SANDBOX_UNAVAILABLE),
    # *A* build in the workspace failed. Lake prints this line for the head
    # tree, for the generated `ChoirBase/*` challenge tree, for a generated
    # lakefile error, and for a Mathlib-from-source build dying after a failed
    # `cache get` — the string itself names no library, so this outcome does
    # **not** establish that the contributor's code is the cause. The
    # attribution ("`rebuild` reports the same root cause") holds only when
    # `rebuild` is also red; see `challenge_side_build_error` and the hedge in
    # `comparator_cli._report_outcome`.
    ("error: build failed", Outcome.SOLUTION_BUILD_FAILED),
)

_CHALLENGE_ERROR_RE = re.compile(rf"{CHALLENGE_PREFIX}/\S*.*\berror:")


def challenge_side_build_error(output: str) -> bool:
    """Does the transcript show a build *error* under `ChoirBase/`?

    A cheap corroborating signal for `SOLUTION_BUILD_FAILED`: the
    `ChoirBase/` tree is generated by Choir from the base SHA, so an error
    there is Choir's own workspace-generation defect, never the
    contributor's diff.

    Requires `error:` on the same line as the path deliberately. A bare
    mention of the prefix proves nothing — Lake prints dotted module names
    (`Built ChoirBase.Proj.Basic`) on every successful build, and the
    challenge tree routinely emits `./ChoirBase/…: warning: declaration uses
    'sorry'` because a sorried target is exactly what a `prove` task's base
    looks like. False negatives are fine (the hedge in the CLI's note covers
    them); a false positive would send a real contributor failure to the
    overseer as infrastructure.
    """
    return any(_CHALLENGE_ERROR_RE.search(line) for line in output.splitlines())

FULL_TRANSCRIPT_OUTCOMES: frozenset[Outcome] = frozenset(
    {Outcome.TOOL_ERROR, Outcome.SOLUTION_BUILD_FAILED, Outcome.SANDBOX_UNAVAILABLE}
)
"""Outcomes where comparator never reached a verdict — the transcript is
the only actionable artifact, so it is carried in full (note 14 diagnosis,
2026-08-18).

Public: this is the seam between the pure classification half of this
module and `comparator_cli.py`'s side-effectful reporting half, which
imports it directly rather than keeping its own duplicate list (fix
round 1, 2026-08-18) — so a new outcome added to this set is picked up by
the CLI's transcript-dump guard automatically, with no second copy to
remember to update."""


def classify_output(exit_code: int, output: str) -> tuple[Outcome, str, str]:
    """Map a comparator run's exit code + combined output to an Outcome.

    The failure strings are comparator's own (Compare.lean / Axioms.lean,
    verified against the v4.31-era source) plus two signatures captured
    live from a real diagnosis session (`could not execute external
    process 'landrun'` for a missing sandbox, `error: build failed` for a
    build that died — usually but *not provably* the solution tree, see
    `_FAILURE_PATTERNS`); anything still unrecognized fails safe to
    TOOL_ERROR. The returned message is the first matching line, or the
    last non-empty output line for MATCH/TOOL_ERROR.

    The third element is the *full* captured output, populated for
    TOOL_ERROR, SOLUTION_BUILD_FAILED, and SANDBOX_UNAVAILABLE. In all
    three, comparator broke or refused rather than rendering a verdict,
    and its one-line summary is routinely uninformative (`uncaught
    exception: Child exited with 1` names neither the child nor the
    cause), so the whole transcript is the only diagnosable artifact.
    """
    if exit_code == 0:
        lines = [ln for ln in output.splitlines() if ln.strip()]
        return Outcome.MATCH, lines[-1] if lines else "comparator accepted", ""
    for pattern, outcome in _FAILURE_PATTERNS:
        for line in output.splitlines():
            if pattern in line:
                full = output if outcome in FULL_TRANSCRIPT_OUTCOMES else ""
                return outcome, line.strip(), full
    lines = [ln for ln in output.splitlines() if ln.strip()]
    message = lines[-1] if lines else f"exit code {exit_code}"
    return Outcome.TOOL_ERROR, message, output
