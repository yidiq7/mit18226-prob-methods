"""CLI: comparator audit on a PR — blocking (design note 14 §6, 8).

Generates a comparator workspace from the PR's base/head SHAs
(`gate.verify.comparator` holds the pure generation logic), then —
when `--comparator-bin` is supplied — runs `lake env <bin> config.json`
inside it and classifies the result.

Two modes, mirroring `trust_report_cli`:

- **PR mode** (`--repo` + `--pr`): resolves the linked issue via the
  Closes/Fixes/Resolves keyword, reads `target_file` + `target_decl`
  from the issue's YAML body, and takes base/head SHAs from the PR.
  This is what `.github/workflows/verify-comparator.yml` invokes.
- **Explicit mode** (`--base-sha --head-sha --target-decl
  --target-file`): no gh, for local runs and tests.

Exit codes:
    0 = verdict rendered and acceptable — match, or any not-applicable /
        not-run path (workspace-generation-only, no --comparator-bin)
    1 = an audit failure the worker owns — statement-mismatch,
        illegal-axiom, solution-build-failed (for the last, `rebuild` is
        expected to be red for the same reason — but only a *red*
        `rebuild` corroborates that; see the printed note)
    2 = comparator could not verify anything — sandbox-unavailable,
        tool-error, or missing-constant (infrastructure faults, not
        contributor ones), or an infra failure before the audit could
        even run (gh/git errors, missing lakefile.toml / lean-toolchain
        at base, unknown prover, workspace write failure, an OSError out
        of the comparator invocation itself)

`missing-constant` sits in the exit-2 group deliberately. The challenge
side of the workspace is built entirely from the base tree plus Choir's
own generator, so nothing in the head tree can add or remove a constant
there: "not found in challenge" means a mis-scoped task or a
workspace-generation gap, not the contributor's code. None of the
missing-constant paths has ever been observed on any machine, and now that
this check blocks a merge the conservative direction is still never to
blame a contributor wrongly — a false escalation is recoverable, a false
accusation is not.

"Not applicable" (still exit 0) covers the note's §6 gates: non-lean4
prover, toolchain below the v4.27 comparator floor, no linked/parseable
task, base tree missing the target **file** (no pre-stated challenge),
reserved lib-name collision. Applicability is decided at *file*
granularity, not declaration granularity: a mis-scoped task naming a
declaration absent from base is still considered applicable, runs, and
reports the cannot-verify `missing-constant` outcome (exit 2) rather than
a clean not-applicable. Tightening that gate to decl level is a
**refinement, not a promotion blocker** (note 14 §8): the scenario that
made it look load-bearing was a worker authoring a statement absent from
base via a `formalize` task, but `formalize` was retired earlier in this
same slice and spec D2 makes the orchestrator the sole statement author —
so a `prove` task naming an absent declaration is now a mis-authored task,
and exit 2 correctly routes that as an infrastructure escalation to the
orchestrator, who owns the task and can fix or drop it.

This check's `CheckClass` is `TRUST` (`gate/checks.py`, note 14 §8) and it
is required-present, so a PR whose head branch deletes this workflow no
longer reads as clean. Its own exit code additionally distinguishes a real
audit failure from an inability to verify, so CI logs and any tooling
reading this process's exit status can tell the two apart even though both
now matter for merging.
"""

from __future__ import annotations

import argparse
import contextlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path

from gate.provers import ProverError
from gate.state.close_on_merge import parse_closing_refs
from gate.state.intake import ParseSuccess, parse_issue_body
from gate.verify.comparator import (
    CHALLENGE_PREFIX,
    FULL_TRANSCRIPT_OUTCOMES,
    ComparatorConfigError,
    Outcome,
    base_module_set,
    challenge_root,
    challenge_side_build_error,
    choirbase_root,
    classify_output,
    comparator_config_json,
    lean_lib_names,
    module_of_path,
    permitted_axioms,
    rewrite_imports,
    solution_root,
    toolchain_supported,
    workspace_lakefile,
)
from gate.verify.config import load_verify_config_at_sha
from gate.verify.prover_dispatch import resolve_prover_profile

_EXCLUDED_PREFIXES = (".lake/", ".choir/", ".github/", "skills/")
_RESERVED_HEAD_FILES = frozenset(
    {"Challenge.lean", "Solution.lean", f"{CHALLENGE_PREFIX}.lean"}
)


class _ExternalError(RuntimeError):
    pass


def _gh(*args: str) -> str:
    result = subprocess.run(
        ["gh", *args], capture_output=True, text=True, check=False
    )
    if result.returncode != 0:
        raise _ExternalError(
            f"gh {' '.join(args)} failed: {(result.stderr or '').strip()}"
        )
    return result.stdout


def _git(*args: str) -> str:
    result = subprocess.run(
        ["git", *args], capture_output=True, text=True, check=False
    )
    if result.returncode != 0:
        raise _ExternalError(
            f"git {' '.join(args)} failed: {(result.stderr or '').strip()}"
        )
    return result.stdout


def _lean_paths(sha: str) -> list[str]:
    """Tracked `.lean` paths at `sha`, minus the non-source trees."""
    paths = []
    for line in _git("ls-tree", "-r", "--name-only", sha).splitlines():
        if not line.endswith(".lean"):
            continue
        if any(line.startswith(prefix) for prefix in _EXCLUDED_PREFIXES):
            continue
        paths.append(line)
    return paths


def _write(dest: Path, text: str) -> None:
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_text(text, encoding="utf-8")


def materialize_workspace(
    base_sha: str,
    head_sha: str,
    target_file: str,
    target_decl: str,
    permitted: tuple[str, ...],
    dest: Path,
) -> Path:
    """Assemble the comparator workspace at `dest`; returns config.json.

    Trusted side: base sources prefixed under `ChoirBase/` with internal
    imports rewritten; lakefile / lean-toolchain / lake-manifest.json
    taken from base only. Untrusted side: head `.lean` sources verbatim,
    except paths that would collide with the generated trusted files
    (`Challenge.lean`, `Solution.lean`, `ChoirBase.lean`, `ChoirBase/…`)
    — those are silently skipped so a PR can't inject content into the
    challenge side of the workspace.

    Runs git in the current working directory (a checkout of the repo),
    like the sibling audit CLIs. Callers validate applicability first;
    this function assumes lakefile.toml and the target file exist at
    base and raises `_ExternalError` / `ComparatorConfigError` on
    surprises.
    """
    base_lakefile = _git("show", f"{base_sha}:lakefile.toml")
    toolchain = _git("show", f"{base_sha}:lean-toolchain")

    base_paths = _lean_paths(base_sha)
    modules = base_module_set(base_paths)
    for path in base_paths:
        content = _git("show", f"{base_sha}:{path}")
        _write(dest / CHALLENGE_PREFIX / path, rewrite_imports(content, modules))

    for path in _lean_paths(head_sha):
        if path in _RESERVED_HEAD_FILES or path.startswith(f"{CHALLENGE_PREFIX}/"):
            continue
        _write(dest / path, _git("show", f"{head_sha}:{path}"))

    _write(dest / "lakefile.toml", workspace_lakefile(base_lakefile))
    _write(dest / "lean-toolchain", toolchain)
    with contextlib.suppress(_ExternalError):  # no manifest = no locked deps
        _write(
            dest / "lake-manifest.json",
            _git("show", f"{base_sha}:lake-manifest.json"),
        )

    root_libs = lean_lib_names(base_lakefile)
    target_module = module_of_path(target_file)
    _write(dest / "Challenge.lean", challenge_root(root_libs, target_module))
    _write(dest / "Solution.lean", solution_root(root_libs, target_module))
    _write(dest / f"{CHALLENGE_PREFIX}.lean", choirbase_root(root_libs))

    config_path = dest / "config.json"
    _write(config_path, comparator_config_json(target_decl, permitted))
    return config_path


def run_comparator(ws: Path, comparator_bin: str) -> tuple[Outcome, str, str]:
    """Run the comparator binary in the workspace and classify the result.

    `lake exe cache get` is attempted first (best-effort) when the manifest
    lists mathlib — comparator's README blesses a trusted Mathlib cache, and
    without one the solution build would rebuild Mathlib from source. A
    *failed* cache get is reported rather than swallowed: it is the most
    likely cause of a slow or exhausted solution build, and the resulting
    tool error would otherwise give no hint of it.

    `COMPARATOR_LANDRUN` / `COMPARATOR_LEAN4EXPORT` are inherited from the
    environment (the workflow sets them). `COMPARATOR_LANDRUN` is
    load-bearing, not optional: comparator has no unsandboxed mode, so
    without a resolvable landrun binary every run tool-errors with
    `could not execute external process 'landrun'`.
    """
    manifest = ws / "lake-manifest.json"
    if manifest.is_file() and "mathlib" in manifest.read_text(encoding="utf-8"):
        cache = subprocess.run(
            ["lake", "exe", "cache", "get"],
            cwd=ws,
            capture_output=True,
            text=True,
            check=False,
        )
        if cache.returncode != 0:
            tail = (cache.stderr or cache.stdout or "").strip().splitlines()
            print(
                "warning: cache get failed — the solution build will compile "
                f"Mathlib from source. {tail[-1] if tail else ''}"
            )
    result = subprocess.run(
        ["lake", "env", comparator_bin, "config.json"],
        cwd=ws,
        capture_output=True,
        text=True,
        check=False,
    )
    output = (result.stdout or "") + "\n" + (result.stderr or "")
    return classify_output(result.returncode, output)


def _report(fields: dict[str, str]) -> None:
    # Promoted to blocking (note 14 §8, gate.checks.CheckClass.TRUST): a
    # nonzero exit here now fails this job, which is a required branch-
    # protection context, so a red outcome below does block the merge.
    print("=== comparator audit (blocking) ===")
    for key, value in fields.items():
        print(f"{key + ':':<14}{value}")


def _not_applicable(reason: str, fields: dict[str, str]) -> int:
    _report({**fields, "outcome": f"not-applicable ({reason})"})
    return 0


def _resolve_pr_target(repo: str, pr: int) -> tuple[str, str, str, str] | str:
    """PR mode: `(base_sha, head_sha, target_file, target_decl)`.

    A returned *string* is a not-applicable reason (no linked issue,
    unparseable body, task without a target). Raises `_ExternalError`
    on gh failures — the caller maps those to exit 2.
    """
    raw = _gh(
        "pr", "view", str(pr), "--repo", repo,
        "--json", "body,baseRefOid,headRefOid",
    )
    pr_meta = json.loads(raw)
    closing = parse_closing_refs(pr_meta.get("body") or "")
    if not closing:
        return "no linked issue"
    issue_body = _gh(
        "issue", "view", str(closing[0]), "--repo", repo,
        "--json", "body", "-q", ".body",
    ).strip()
    parsed = parse_issue_body(issue_body, expected_repo=repo)
    if not isinstance(parsed, ParseSuccess):
        return f"issue #{closing[0]} body fails to parse"
    if not parsed.record.target_file or not parsed.record.target_decl:
        return "task carries no target_file/target_decl"
    return (
        pr_meta["baseRefOid"],
        pr_meta["headRefOid"],
        parsed.record.target_file,
        parsed.record.target_decl,
    )


def _applicability_reason(base_sha: str, target_file: str) -> str | None:
    """Note 14 §6 gates 2–4 (prover is gate 1, checked by the caller).

    None = applicable. A string = not-applicable reason. Raises
    `_ExternalError` when the base tree is missing lean-toolchain or
    lakefile.toml — a lean4 project without either is infrastructure
    breakage, not a benign skip.

    The target gate is **file**-level, not declaration-level: a task whose
    `target_decl` does not exist at base still reads as applicable so long
    as its `target_file` does, and reaches comparator's cannot-verify
    `missing-constant` outcome. Tightening this to decl level is a
    refinement, not a promotion blocker (note 14 §8) — comparator already
    shipped as blocking.
    """
    toolchain = _git("show", f"{base_sha}:lean-toolchain")
    supported = toolchain_supported(toolchain)
    if supported is not True:
        detail = "unparseable" if supported is None else "below comparator floor v4.27"
        return f"toolchain {toolchain.strip()!r} {detail}"

    base_lakefile = _git("show", f"{base_sha}:lakefile.toml")
    try:
        workspace_lakefile(base_lakefile)
    except ComparatorConfigError as e:
        return str(e)

    try:
        _git("show", f"{base_sha}:{target_file}")
    except _ExternalError:
        return f"{target_file} not present at base — no pre-stated challenge"
    return None


# ---------------------------------------------------------------------------
# exit-code classification (see the module docstring for the contract)
# ---------------------------------------------------------------------------

_WORKER_FAILURES = frozenset(
    {
        Outcome.STATEMENT_MISMATCH,
        Outcome.ILLEGAL_AXIOM,
        Outcome.SOLUTION_BUILD_FAILED,
    }
)
_INFRA_FAILURES = frozenset(
    {
        Outcome.SANDBOX_UNAVAILABLE,
        Outcome.TOOL_ERROR,
        # Not the contributor's: the challenge environment comes from the base
        # tree plus this module's generator, so a head tree cannot change which
        # constants exist in it. See the module docstring.
        Outcome.MISSING_CONSTANT,
    }
)
# Transcript-carrying outcomes are `comparator.py`'s call, not a second copy
# here (fix round 1, 2026-08-18) — see `FULL_TRANSCRIPT_OUTCOMES`'s docstring.


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Comparator audit (blocking, lean4-only)"
    )
    parser.add_argument("--repo", help="owner/name (PR mode)")
    parser.add_argument("--pr", type=int, help="PR number (PR mode)")
    parser.add_argument("--base-sha", help="explicit mode")
    parser.add_argument("--head-sha", help="explicit mode")
    parser.add_argument("--target-decl", help="explicit mode")
    parser.add_argument("--target-file", help="explicit mode")
    parser.add_argument(
        "--prover",
        default=None,
        help="Override the effective prover. Default: read "
        "[project].prover from .choir/project.toml at the PR's base SHA, "
        "else lean4.",
    )
    parser.add_argument(
        "--workspace-dir",
        default=None,
        help="Where to generate the workspace (default: fresh temp dir).",
    )
    parser.add_argument(
        "--comparator-bin",
        default=None,
        help="Path to the comparator binary. Absent: generate the "
        "workspace, report not-run, exit 0.",
    )
    return parser


def _report_outcome(
    fields: dict[str, str], outcome: Outcome, message: str, full: str
) -> int:
    """Print the report + whose-problem note + transcript; map to exit code.

    Split out of `main` so the exit-code/report logic (see the module
    docstring's contract) is one focused function, not another branch
    stacked onto `main`'s tail.

    The whose-problem note prints *before* the raw transcript dump (fix
    round 1, 2026-08-18) so a reader scanning top-to-bottom is told how to
    interpret the output before meeting it, not after.
    """
    _report({**fields, "outcome": outcome.value, "detail": message})

    if outcome is Outcome.SOLUTION_BUILD_FAILED:
        print(
            "note: a build in the comparator workspace failed. **Check "
            "`rebuild` before triaging this.** If `rebuild` is also red, "
            "that check owns the diagnostics and this is one failure "
            "surfacing in two checks, not two independent problems. If "
            "`rebuild` is GREEN, the head tree compiles fine and the "
            "failure is in comparator's own generated workspace "
            f"({CHALLENGE_PREFIX}/ challenge tree, generated lakefile, or a "
            "Mathlib-from-source build after a failed cache get) — that is "
            "an infrastructure fault to escalate, not a duplicate to "
            "dismiss."
        )
        if challenge_side_build_error(full):
            print(
                f"note: the transcript reports an error under {CHALLENGE_PREFIX}/, "
                "which Choir generates from the base SHA — the contributor's "
                "diff cannot reach it. Treat this as a workspace-generation "
                "fault and escalate."
            )
    elif outcome in _INFRA_FAILURES:
        print(
            "note: comparator could not verify anything — this is an "
            "infrastructure fault, not a contributor one. It needs "
            "overseer escalation, not rejecting the PR."
        )
    elif outcome in _WORKER_FAILURES:
        print(
            "note: this is an audit failure the PR owns — comparator "
            "rendered a real verdict against the published statement, and "
            "this check now blocks the merge (design note 14 §8)."
        )

    if outcome in FULL_TRANSCRIPT_OUTCOMES and full.strip():
        print(f"--- comparator output ({outcome.value}) ---")
        print(full.rstrip())
        print("--- end comparator output ---")

    if outcome in _WORKER_FAILURES:
        return 1
    if outcome in _INFRA_FAILURES:
        return 2
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = _build_parser()
    args = parser.parse_args(argv)

    pr_mode = args.repo is not None and args.pr is not None
    explicit_mode = all(
        getattr(args, name) is not None
        for name in ("base_sha", "head_sha", "target_decl", "target_file")
    )
    if not pr_mode and not explicit_mode:
        parser.error(
            "need --repo/--pr, or all of --base-sha/--head-sha/"
            "--target-decl/--target-file"
        )

    if pr_mode:
        try:
            resolved = _resolve_pr_target(args.repo, args.pr)
        except _ExternalError as e:
            print(f"error: {e}", file=sys.stderr)
            return 2
        if isinstance(resolved, str):
            return _not_applicable(resolved, {})
        base_sha, head_sha, target_file, target_decl = resolved
    else:
        base_sha = args.base_sha
        head_sha = args.head_sha
        target_file = args.target_file
        target_decl = args.target_decl

    fields = {"target_decl": target_decl, "target_file": target_file}

    try:
        profile = resolve_prover_profile(args.prover, base_sha)
    except ProverError as e:
        print(f"error: {e}", file=sys.stderr)
        return 2
    fields = {"prover": profile.name, **fields}
    if profile.name != "lean4":
        return _not_applicable(
            f"prover is {profile.name} — comparator is lean4-only", fields
        )

    try:
        reason = _applicability_reason(base_sha, target_file)
    except _ExternalError as e:
        print(f"error: {e}", file=sys.stderr)
        return 2
    if reason is not None:
        return _not_applicable(reason, fields)

    permitted = permitted_axioms(load_verify_config_at_sha(base_sha))
    ws = Path(
        args.workspace_dir
        if args.workspace_dir is not None
        else tempfile.mkdtemp(prefix="choir-comparator-")
    )
    try:
        materialize_workspace(
            base_sha, head_sha, target_file, target_decl, permitted, ws
        )
    except (_ExternalError, ComparatorConfigError, OSError) as e:
        print(f"error: workspace generation failed — {e}", file=sys.stderr)
        return 2
    fields["workspace"] = str(ws)
    fields["permitted"] = ", ".join(permitted)

    if args.comparator_bin is None:
        _report(
            {**fields, "outcome": "not-run (generation only — no --comparator-bin)"}
        )
        return 0

    try:
        outcome, message, full = run_comparator(ws, args.comparator_bin)
    except OSError as e:
        # `lake` absent from PATH, an unreadable manifest, a workspace that
        # vanished — infrastructure, and exit 1 is reserved for "the
        # contributor owns this", which an interpreter traceback would
        # otherwise claim on their behalf.
        print(f"error: comparator invocation failed — {e}", file=sys.stderr)
        return 2
    return _report_outcome(fields, outcome, message, full)


if __name__ == "__main__":
    sys.exit(main())
