"""Contributor-side configuration read from `~/.choir/config.json`.

The file is optional — when absent, defaults apply (manual backend).
`$CHOIR_CONFIG` overrides the path, mostly for tests.

Schema (v0)::

    {
      "backend": {
        "type": "manual" | "script",
        "command": ["claude", "code"]   // required when type == "script"
      },
      "tooling": {
        "search": "lean-lsp-mcp" | "backend-provided" | "none"  // optional
      },
      "worker": {
        "accept_types": ["prove", "golf"],  // optional; None = all types; default ["prove", "golf"]
        "max_difficulty": "easy" | "medium" | "hard",  // optional; None = no cap
        "auto_update": "required" | "always" | "never"  // optional; default "required"
      }
    }
"""

from __future__ import annotations

import json
import os
from dataclasses import dataclass, field
from pathlib import Path


class ConfigError(RuntimeError):
    """A config file exists but its contents are malformed."""


@dataclass
class BackendConfig:
    type: str
    command: list[str] | None = None


@dataclass
class ToolingConfig:
    search: str | None = None


@dataclass
class WorkerConfig:
    """Worker-loop appetite (design note 11 §4) + auto-update policy
    (design note 13 §6).

    `load_config()` maps an absent `accept_types` key to `["prove", "golf"]`
    (index is Phase 5, not yet a publish path; review no longer exists —
    spec D1 removed the task type entirely). Explicit `None`
    means accept ALL task types. `max_difficulty=None` means no cap; unrated
    tasks pass every cap. `auto_update` governs how the headless worker reacts
    to `IterationResult.PROTOCOL_STALE`: `"required"` (default) updates + re-execs
    only when the hard gate trips; `"always"` additionally checks at loop start
    whenever origin moved; `"never"` exits with an instruction instead of updating
    itself.
    """

    # None here means unresolved; load_config() applies the actual default.
    accept_types: list[str] | None = None
    max_difficulty: str | None = None
    auto_update: str = "required"


@dataclass
class Config:
    backend: BackendConfig
    tooling: ToolingConfig = field(default_factory=ToolingConfig)
    worker: WorkerConfig = field(default_factory=WorkerConfig)

    @classmethod
    def default(cls) -> Config:
        return cls(backend=BackendConfig(type="manual"), tooling=ToolingConfig())


def config_path() -> Path:
    """Path to the machine-global config (default backend + tooling.search)."""
    override = os.environ.get("CHOIR_CONFIG")
    if override:
        return Path(override).expanduser()
    return Path.home() / ".choir" / "config.json"


def project_config_path(repo: str) -> Path:
    """Per-project backend override: ``<.choir>/projects/<owner>/<name>/config.json``.

    Lives as a sibling of the global config under the same ``.choir`` root, so a
    ``$CHOIR_CONFIG`` redirect (used by tests) moves both together. A contributor
    who wants a different agent/model on one project drops a file here; otherwise
    the global config applies to every project unchanged.
    """
    root = config_path().parent
    owner, _, name = repo.partition("/")
    return root / "projects" / owner / name / "config.json"


def _read_json_object(path: Path) -> dict:
    """Read a JSON object from ``path``; ``{}`` if absent. Raises on malformed."""
    if not path.is_file():
        return {}
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as e:
        raise ConfigError(f"{path}: {e}") from e
    if not isinstance(data, dict):
        raise ConfigError(f"{path}: top-level must be a JSON object")
    return data


def load_config(repo: str | None = None) -> Config:
    """Read contributor config, optionally overlaying a per-project override.

    With no ``repo`` (or none configured), reads only the machine-global
    ``~/.choir/config.json`` — defaults (manual backend) if it's absent. When
    ``repo`` is given and ``~/.choir/projects/<owner>/<name>/config.json``
    exists, its top-level keys overlay the global: a per-project ``backend``
    wins while ``tooling`` is inherited from the global (``tooling.search`` is a
    machine fact, not a per-project one, so callers that only need it pass no
    repo).
    """
    global_path = config_path()
    data = _read_json_object(global_path)
    source = str(global_path)
    if repo and "/" in repo:
        proj_path = project_config_path(repo)
        proj = _read_json_object(proj_path)
        if proj:
            data = {**data, **proj}  # per-project top-level keys win
            source = f"{global_path} + {proj_path}"
    return _parse_config(data, source)


def _parse_config(data: dict, source: str) -> Config:
    backend_data = data.get("backend") or {}
    if not isinstance(backend_data, dict):
        raise ConfigError(f"{source}: 'backend' must be an object")

    tooling_data = data.get("tooling") or {}
    if not isinstance(tooling_data, dict):
        raise ConfigError(f"{source}: 'tooling' must be an object")
    search = tooling_data.get("search")
    if search is not None and not isinstance(search, str):
        raise ConfigError(f"{source}: 'tooling.search' must be a string")
    tooling = ToolingConfig(search=search)

    worker_data = data.get("worker") or {}
    if not isinstance(worker_data, dict):
        raise ConfigError(f"{source}: 'worker' must be an object")
    # Default to ["prove", "golf"] if absent; explicit None still means all types.
    if "accept_types" in worker_data:
        accept_types = worker_data.get("accept_types")
    else:
        accept_types = ["prove", "golf"]
    if accept_types is not None and (
        not isinstance(accept_types, list)
        or not all(isinstance(x, str) for x in accept_types)
    ):
        raise ConfigError(f"{source}: 'worker.accept_types' must be a list of strings")
    max_difficulty = worker_data.get("max_difficulty")
    if max_difficulty is not None and max_difficulty not in ("easy", "medium", "hard"):
        raise ConfigError(
            f"{source}: 'worker.max_difficulty' must be one of easy|medium|hard"
        )
    auto_update = worker_data.get("auto_update", "required")
    if auto_update not in ("required", "always", "never"):
        raise ConfigError(
            f"{source}: 'worker.auto_update' must be one of required|always|never"
        )
    worker = WorkerConfig(
        accept_types=accept_types,
        max_difficulty=max_difficulty,
        auto_update=auto_update,
    )

    btype = backend_data.get("type", "manual")
    if btype == "manual":
        return Config(backend=BackendConfig(type="manual"), tooling=tooling, worker=worker)
    if btype == "script":
        cmd = backend_data.get("command")
        if not isinstance(cmd, list) or not cmd or not all(isinstance(x, str) for x in cmd):
            raise ConfigError(
                f"{source}: backend.type='script' requires 'command' as a "
                "non-empty list of strings"
            )
        return Config(
            backend=BackendConfig(type="script", command=list(cmd)),
            tooling=tooling,
            worker=worker,
        )
    raise ConfigError(f"{source}: unknown backend type {btype!r}")
