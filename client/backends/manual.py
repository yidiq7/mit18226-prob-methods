"""Manual backend: print instructions, exit. The contributor does the work."""

from __future__ import annotations

from pathlib import Path

from client.backends import Backend
from client.workspace import workspace_profile


class ManualBackend(Backend):
    def run(self, *, workspace: Path, task_md: str) -> int:
        del task_md  # TASK.md already lives at workspace/TASK.md
        build_cmd = " ".join(workspace_profile(workspace).build_command)
        print()
        print(f"Workspace: {workspace}")
        print()
        print("This workspace is set up for manual work:")
        print("  1. Open TASK.md to read the task description.")
        print(f"  2. Edit the target file(s), run {build_cmd} to verify.")
        print("  3. Commit your changes.")
        print("  4. Run `choir submit` to push and open the PR.")
        return 0
