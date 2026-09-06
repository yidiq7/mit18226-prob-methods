"""The contributor joining prompt — hardcoded, never composed by the agent.

The orchestrator prints this for the overseer to hand to contributor
machines:

    uv run python -m orchestrator.joining_prompt <owner/repo>

All mechanical setup lives in `scripts/join.sh`; the behavioral contract
lives in `docs/agents/CONTRIBUTOR.md`. The prompt only points at both, so it
stays a few lines no matter how the mechanics evolve.
"""

from __future__ import annotations

import argparse
import sys

DEFAULT_CHOIR_URL = "git@github.com:yidiq7/choir.git"

_TEMPLATE = """\
You are a Choir contributor (worker agent) for the project **`{repo}`**.

1. Set up: `git clone {choir_url} ./choir 2>/dev/null; sh ./choir/scripts/join.sh {repo} --backend <agent>`
   `<agent>` = the agent you are: `claude` | `codex` | `vibe`. Anything else (or a
   prover your user named): omit `--backend` and follow `./choir/docs/agents/BACKENDS.md`
   § "Wiring a specialized prover"; verify with `choir backend check`.
   Fix anything the script flags and re-run until it reports READY.
2. Start the worker loop it prints — `cd ./choir && uv run choir worker {repo}` —
   and keep it running unattended (background it or use a terminal multiplexer).
3. Read `./choir/docs/agents/CONTRIBUTOR.md` and work by it. The short version: report
   claims and submitted PRs to your user as they happen; your LLM credentials
   never leave this machine.\
"""  # noqa: E501


def joining_prompt(repo: str, choir_url: str | None = None) -> str:
    """Render the canonical joining prompt for ``repo`` (``owner/name``)."""
    return _TEMPLATE.format(repo=repo, choir_url=choir_url or DEFAULT_CHOIR_URL)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        prog="python -m orchestrator.joining_prompt",
        description="Print the contributor joining prompt for a project repo.",
    )
    parser.add_argument("repo", help="GitHub repo as owner/name")
    parser.add_argument(
        "--choir-url",
        default=DEFAULT_CHOIR_URL,
        help="Choir repo URL contributors clone (default: %(default)s)",
    )
    try:
        args = parser.parse_args(argv)
    except SystemExit as e:
        return int(e.code or 0) or 2
    print(joining_prompt(args.repo, choir_url=args.choir_url))
    return 0


if __name__ == "__main__":
    sys.exit(main())
