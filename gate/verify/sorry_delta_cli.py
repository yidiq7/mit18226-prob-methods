"""CLI: sorry-delta (placeholder-delta) audit on a PR.

Invoked by `.github/workflows/verify-sorry.yml`. Reads the PR's changed
files via the shared `gate.verify.pr_files.fetch_pr_files` (paginated
past `gh pr view --json files`'s 100-file cap), fetches base and head
versions of each prover source file via `git show`, and runs
`sorry_delta.compare`. The check name (`verify-sorry`) stays the
prover-neutral name across all three profiles (design note 12 §2.3);
what counts as a "sorry" — the placeholder tokens and file extensions
scanned — comes from the effective `ProverProfile` (`--prover` flag >
base-SHA `.choir/project.toml` > lean4 default, resolved once via
`gate.verify.prover_dispatch.resolve_prover_profile`).

The sorry policy comes from `.choir/verify.toml` at the **base** SHA
(a PR can't flip its own project to `report` mode):

- `block` (default): net-new placeholders fail the check.
- `report`: net-new placeholders are listed but the check passes —
  blueprint-style projects where partial progress may merge after
  orchestrator review.

Exit codes:
    0 = audit passes (no net-new placeholders, or policy is `report`)
    1 = audit fails (net-new placeholders under `block`; merge blocked)
    2 = environmental failure (gh/git error, or an unresolvable prover)
"""

from __future__ import annotations

import argparse
import subprocess
import sys

from gate.provers import ProverError
from gate.verify.config import SorryPolicy, VerifyConfig, load_verify_config_at_sha
from gate.verify.pr_files import PrFilesError, fetch_pr_files
from gate.verify.prover_dispatch import filter_files_by_profile, resolve_prover_profile
from gate.verify.sorry_delta import Verdict, compare, format_finding

# Re-exported under the audit-conventional name (mirrors
# axiom_honesty_cli); reads from the base SHA by contract.
load_verify_config_from_base = load_verify_config_at_sha


def exit_code_for(*, any_introduced: bool, policy: SorryPolicy) -> int:
    """Map the audit outcome to the process exit code.

    `report` never fails the check: the delta is information for the
    orchestrator's review, not a merge-blocker.
    """
    if any_introduced and policy is SorryPolicy.BLOCK:
        return 1
    return 0


class _ExternalError(RuntimeError):
    pass


def _run(tool: str, *args: str) -> str:
    result = subprocess.run(
        [tool, *args], capture_output=True, text=True, check=False
    )
    if result.returncode != 0:
        raise _ExternalError(
            f"{tool} {' '.join(args)} failed: {(result.stderr or '').strip()}"
        )
    return result.stdout


def _show(sha: str, path: str) -> str:
    """Contents of `path` at `sha`, or '' if not present (new file)."""
    try:
        return _run("git", "show", f"{sha}:{path}")
    except _ExternalError:
        return ""


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Sorry-delta audit")
    parser.add_argument("--repo", required=True)
    parser.add_argument("--pr", required=True, type=int)
    parser.add_argument(
        "--prover",
        default=None,
        help="Override the effective prover. Default: read "
        "[project].prover from .choir/project.toml at the PR's base SHA, "
        "else lean4.",
    )
    args = parser.parse_args(argv)

    try:
        base_sha, head_sha, all_files = fetch_pr_files(args.repo, args.pr)
    except (PrFilesError, _ExternalError) as e:
        # PrFilesError is what the shared fetch actually raises;
        # _ExternalError (this module's own git/gh-failure type, used
        # below by `_show`) is caught too so this call site keeps
        # mapping any external-command failure to exit 2, however it's
        # signaled.
        print(f"error: {e}", file=sys.stderr)
        return 2

    try:
        profile = resolve_prover_profile(args.prover, base_sha)
    except ProverError as e:
        # An unresolvable prover (unknown --prover, or malformed
        # [project] prover in the base-SHA .choir/project.toml) is an
        # infrastructure failure, not "the contributor introduced a
        # placeholder" — must not fall through to Python's default
        # exit 1, which the exit contract reserves for the latter.
        print(f"error: {e}", file=sys.stderr)
        return 2
    files = filter_files_by_profile(all_files, profile)

    config: VerifyConfig = load_verify_config_from_base(base_sha)
    policy = config.sorry_delta.policy

    print("=== sorry-delta audit ===")
    print(f"prover: {profile.name}")
    print(f"base: {base_sha}")
    print(f"head: {head_sha}")
    print(f"policy: {policy.value}")
    print(f"changed {'/'.join(profile.file_extensions)} files: {len(files)}")
    print()

    if not files:
        print("No matching source files changed; audit not applicable.")
        return 0

    any_introduced = False
    for path in files:
        base = _show(base_sha, path)
        head = _show(head_sha, path)
        verdict, finding = compare(base, head, file_path=path, profile=profile)
        if verdict == Verdict.INTRODUCED:
            any_introduced = True
            print(f"⚠ {path}: net-new placeholders")
            assert finding is not None
            print(format_finding(finding))
            print()
        else:
            print(f"✓ {path}: clean")

    if any_introduced:
        print()
        if policy is SorryPolicy.BLOCK:
            print(
                "PR increases the number of placeholder proofs (sorry / "
                "oops / Admitted, per prover). The build treats these as "
                "warnings, not errors, so this audit is the merge-blocker: "
                "final submissions must not add unproven obligations. If "
                "this is an intentional progress checkpoint, coordinate "
                "with the project overseer."
            )
        else:
            print(
                "PR increases the number of placeholder proofs. Project "
                "policy is `report`: the check passes, and whether this "
                "partial progress merges is the orchestrator's review "
                "decision. Merged placeholders enter the trust inventory "
                "as open obligations."
            )

    return exit_code_for(any_introduced=any_introduced, policy=policy)


if __name__ == "__main__":
    sys.exit(main())
