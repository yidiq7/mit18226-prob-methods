"""Agent backend abstraction.

A backend takes a workspace path and runs whatever it runs — print
manual instructions, invoke `claude code`, shell out to OpenGauss, etc.
The contributor configures the backend via `~/.choir/config.json`. The
CLI dispatches to the configured backend during `choir work`.

The minimal interface is a `run(workspace, task_md)` method that
returns an exit code. Backends are responsible for any I/O they need;
the CLI's only job is to invoke the backend and act on its exit code.
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from pathlib import Path


class Backend(ABC):
    @abstractmethod
    def run(self, *, workspace: Path, task_md: str) -> int:
        """Run the backend in `workspace`. Return process exit code."""


def get_backend(backend_type: str, *, command: list[str] | None = None) -> Backend:
    """Construct a backend by configured type.

    Raises `ValueError` for unknown types. `script` requires `command`.
    """
    # Lazy imports avoid circular-import issues — each concrete backend
    # imports `Backend` from this module.
    if backend_type == "manual":
        from client.backends.manual import ManualBackend  # noqa: PLC0415

        return ManualBackend()
    if backend_type == "script":
        if command is None:
            raise ValueError("script backend requires a command")
        from client.backends.script import ScriptBackend  # noqa: PLC0415

        return ScriptBackend(command=command)
    raise ValueError(f"unknown backend type: {backend_type!r}")
