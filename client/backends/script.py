"""Script backend: run a configured shell command in the workspace.

The command is a list of strings — argv, not a shell string — so it
runs without shell interpretation. To use a backend like Claude Code::

    ~/.choir/config.json:
    {
      "backend": {"type": "script", "command": ["claude", "code"]}
    }

The backend exits with the child process's exit code. Choir does not
proxy or inspect the child's stdout/stderr; the contributor sees what
the agent says directly.
"""

from __future__ import annotations

import os
import subprocess
from pathlib import Path

from client.backends import Backend


class ScriptBackend(Backend):
    def __init__(self, *, command: list[str]) -> None:
        self.command = command

    def run(self, *, workspace: Path, task_md: str) -> int:
        del task_md  # backends read TASK.md themselves if they want it
        env = os.environ.copy()
        context = workspace / ".choir-context.md"
        skills = workspace / ".choir-skills"
        if context.is_file():
            env["CHOIR_CONTEXT"] = str(context)
        if skills.is_dir():
            env["CHOIR_SKILLS"] = str(skills)
        print(f"Running `{' '.join(self.command)}` in {workspace}...")
        try:
            result = subprocess.run(self.command, cwd=workspace, check=False, env=env)
        except FileNotFoundError:
            print(
                f"error: command not found: {self.command[0]} "
                "(check that it's installed and on PATH)"
            )
            return 127
        return result.returncode
