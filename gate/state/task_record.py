"""TaskRecord model — the machine-readable contract embedded in every Choir issue.

This module is the source of truth for the v1 schema.
"""

from __future__ import annotations

import re
from enum import StrEnum
from typing import Literal

from pydantic import BaseModel, ConfigDict, Field, field_validator, model_validator


# Retired 2026-08-18 — do not re-add: `formalize` named a workflow spec D2
# forbids (the orchestrator authors every statement; workers only fill
# placeholders), `draft` and `refactor` had no plan behind them and zero
# live use across all live projects, and `review` was removed by spec D1
# (the review layer is retired — the orchestrator reviews every PR
# itself). `index` stays (Phase 5 coherence indexer).
class TaskType(StrEnum):
    """The kind of work a task asks for. `index` is reserved for the
    coherence indexer and is excluded from the worker default."""

    PROVE = "prove"
    GOLF = "golf"
    INDEX = "index"


_TARGET_DECL_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_.']*$")
_COMMIT_RE = re.compile(r"^[0-9a-f]{7,}$")
_REPO_RE = re.compile(r"^[^/\s]+/[^/\s]+$")


class ProjectRef(BaseModel):
    """The exact tree a task is pinned to: repo, commit, and toolchain.

    Workers build against this, so it is what makes a task reproducible.
    """

    model_config = ConfigDict(extra="forbid", str_strip_whitespace=True)

    repo: str
    commit: str
    toolchain: str

    @field_validator("repo", mode="before")
    @classmethod
    def _normalize_repo(cls, v: object) -> object:
        if not isinstance(v, str):
            return v
        stripped = v.strip()
        if "/" in stripped:
            owner, _, name = stripped.partition("/")
            return f"{owner.lower()}/{name}"
        return stripped

    @field_validator("repo")
    @classmethod
    def _check_repo_shape(cls, v: str) -> str:
        if not _REPO_RE.match(v):
            raise ValueError("repo must be of the form '<owner>/<name>'")
        return v

    @field_validator("commit", mode="before")
    @classmethod
    def _normalize_commit(cls, v: object) -> object:
        if isinstance(v, str):
            return v.strip().lower()
        return v

    @field_validator("commit")
    @classmethod
    def _check_commit_shape(cls, v: str) -> str:
        if not _COMMIT_RE.match(v):
            raise ValueError("commit must be 7+ lowercase hex characters")
        return v


class TaskRecord(BaseModel):
    """A v1 Choir task record. See design note 02."""

    model_config = ConfigDict(
        extra="forbid",
        str_strip_whitespace=True,
        populate_by_name=True,
    )

    choir_task_version: Literal[1] = Field(alias="choir-task-version")
    type: TaskType
    target_file: str | None = None
    target_decl: str | None = None
    project_ref: ProjectRef
    deps: list[int]
    blueprint_ref: str | None = None

    @field_validator("target_file", mode="before")
    @classmethod
    def _normalize_target_file(cls, v: object) -> object:
        if not isinstance(v, str):
            return v
        s = v.strip()
        if s.startswith("./"):
            s = s[2:]
        return s

    @field_validator("target_file")
    @classmethod
    def _check_target_file(cls, v: str) -> str:
        if v is None:
            return v
        if not v:
            raise ValueError("target_file must not be empty")
        if v.startswith("/"):
            raise ValueError("target_file must be a repo-relative path, not absolute")
        if "\\" in v:
            raise ValueError("target_file must use forward slashes, not backslashes")
        if ".." in v.split("/"):
            raise ValueError("target_file must not contain '..' segments")
        return v

    @field_validator("target_decl")
    @classmethod
    def _check_target_decl(cls, v: str) -> str:
        if v is None:
            return v
        if not _TARGET_DECL_RE.match(v):
            raise ValueError(
                "target_decl must match identifier rules "
                "(letters, digits, underscores, dots, apostrophes; not starting with a digit)"
            )
        return v

    @field_validator("deps")
    @classmethod
    def _check_deps(cls, v: list[int]) -> list[int]:
        for n in v:
            if n <= 0:
                raise ValueError("deps entries must be positive integers (GitHub issue numbers)")
        return v

    @model_validator(mode="after")
    def _check_target_by_type(self) -> TaskRecord:
        """Every task type requires a declaration in a file.

        Pre-spec-D1 this branched on `type: review` (which pointed at a PR
        via `target_pr` instead); spec D1 removed the review task type, so
        every remaining type (prove/golf/index) takes the same shape.
        """
        if not self.target_file or not self.target_decl:
            raise ValueError(
                f"type: {self.type.value} requires target_file and target_decl"
            )
        return self
