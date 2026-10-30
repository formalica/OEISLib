"""Runs `lake build` on generated modules and attributes diagnostics back to items."""

from __future__ import annotations

import os
import re
import shutil
import subprocess
from dataclasses import dataclass, field
from pathlib import Path

from .config import REPO_ROOT

DIAG = re.compile(r"^(error|warning|info): (?:\./)?([^\s:]+\.lean):(\d+):(\d+): (.*)$")
CHECK_FAIL = re.compile(r"OEIS_CHECK_FAIL\s+(A\d{6}):\s*(.*)$", re.MULTILINE)
DEP_RANGE = re.compile(r"OEIS_DEP_RANGE\s+(A\d{6})\s+needs\s+(A\d{6})\s+n=(-?\d+)")
MISMATCH = re.compile(r"n=(-?\d+): expected (-?\d+), got (-?\d+)")


def lake_binary() -> str:
    found = shutil.which("lake")
    if found:
        return found
    candidate = Path.home() / ".elan" / "bin" / "lake"
    if candidate.exists():
        return str(candidate)
    raise RuntimeError("`lake` not found; install elan or add it to PATH")


@dataclass
class BuildResult:
    ok: bool
    timed_out: bool
    output: str
    per_file: dict[str, list[str]] = field(default_factory=dict)

    def diagnostics_for(self, *paths: str) -> list[str]:
        out: list[str] = []
        for p in paths:
            if p:
                out.extend(self.per_file.get(p, []))
        return out


def _attribute(output: str) -> dict[str, list[str]]:
    per_file: dict[str, list[str]] = {}
    current: list[str] | None = None
    for line in output.splitlines():
        m = DIAG.match(line.strip())
        if m:
            kind, path, _, _, _ = m.groups()
            current = per_file.setdefault(path, []) if kind == "error" else None
            if current is not None:
                current.append(line.rstrip())
            continue
        if line.startswith(("✔", "✖", "⚠", "ℹ", "info:", "warning:", "trace:",
                            "Build completed", "Some required targets", "- Check.",
                            "- OEISLib.")):
            current = None
            continue
        if current is not None:
            current.append(line.rstrip())
    return per_file

def build(targets: list[str], timeout: int) -> BuildResult:
    if not targets:
        return BuildResult(ok=True, timed_out=False, output="")
    env = dict(os.environ)
    env["PATH"] = f"{Path.home() / '.elan' / 'bin'}:{env.get('PATH', '')}"
    try:
        proc = subprocess.run(
            [lake_binary(), "build", *targets],
            cwd=REPO_ROOT,
            env=env,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired as exc:
        output = (exc.stdout or "") + (exc.stderr or "")
        if isinstance(output, bytes):
            output = output.decode("utf-8", "replace")
        return BuildResult(ok=False, timed_out=True, output=output)
    output = proc.stdout + proc.stderr
    return BuildResult(
        ok=proc.returncode == 0, timed_out=False, output=output, per_file=_attribute(output)
    )


def dep_range_failures(output: str, owner: str) -> list[str]:
    """Panics raised when a translation asked a dependency for an index OEIS does not list.

    These are printed by the running `#eval`, not attributed to a source file, so they are
    matched against the whole build output.
    """
    seen: dict[str, str] = {}
    for who, dep, n in DEP_RANGE.findall(output):
        if who == owner:
            seen.setdefault(
                dep,
                f"the translation needs {dep}({n}), beyond the terms OEIS lists for {dep}",
            )
    return list(seen.values())


def parse_failure_points(diagnostics: list[str], offset: int) -> list[dict[str, str]]:
    """Extracts the OEIS indices at which a formalization disagrees with the data."""
    points: list[dict[str, str]] = []
    text = "\n".join(diagnostics)
    fail = CHECK_FAIL.search(text)
    if fail:
        for n, expected, got in MISMATCH.findall(fail.group(2)):
            points.append({"n": n, "expected": expected, "got": got})
    if not points:
        for m in re.finditer(r"\bcheck_(\d+)\b", text):
            points.append({"n": str(offset + int(m.group(1)))})
    return points
