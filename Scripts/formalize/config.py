"""Paths, environment and per-run tuning knobs."""

from __future__ import annotations

import os
from dataclasses import dataclass
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]

DEFAULT_DB = REPO_ROOT / "Metadata" / "oeis.db"
DEFAULT_OEISLib = REPO_ROOT / "OEISLib"
DEFAULT_CHECK = REPO_ROOT / "Check"
DEFAULT_SKILLS = REPO_ROOT / "Skills"

OEISLib_LIB = "OEISLib"
CHECK_LIB = "Check"


@dataclass
class Config:
    db_path: Path = DEFAULT_DB
    loeis_dir: Path = DEFAULT_OEISLib
    check_dir: Path = DEFAULT_CHECK
    skills_dir: Path = DEFAULT_SKILLS
    language: str = "maple"
    model_name: str = "anthropic:claude-sonnet-4-5"
    base_url: str | None = None
    api_key: str | None = None
    terms: int = 20
    build_timeout: int = 900
    keep_check_files: bool = False

    @classmethod
    def from_env(cls, **overrides: object) -> "Config":
        cfg = cls(
            model_name=os.environ.get("OEIS_LLM_MODEL", cls.model_name),
            base_url=os.environ.get("OEIS_LLM_BASE_URL") or os.environ.get("OPENAI_BASE_URL"),
            api_key=os.environ.get("OEIS_LLM_API_KEY") or os.environ.get("OPENAI_API_KEY"),
        )
        for key, value in overrides.items():
            if value is not None:
                setattr(cfg, key, value)
        return cfg

    @property
    def skill_dir(self) -> Path:
        return self.skills_dir / self.language
