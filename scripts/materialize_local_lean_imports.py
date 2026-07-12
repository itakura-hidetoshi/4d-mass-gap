#!/usr/bin/env python3
"""Materialize only direct missing local Lean imports for changed leaf files.

A newly merged leaf may be absent from the restored cache.  Compiling the full
transitive local closure can exceed the fast-check budget, so this helper emits
only missing direct MGAP4D imports.  Compiler diagnostics are mirrored to the
standard fast-check artifact path.
"""

from __future__ import annotations

import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path.cwd()
BUILD_LIB = ROOT / ".lake" / "build" / "lib" / "lean"
IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_'.]+)\s*$")
AGGREGATE_ROOTS = {Path("MGAP4D.lean"), Path("MGAP4D/MathlibAnalytic.lean")}


def changed_lean_files(base: str) -> list[Path]:
    commands = [
        ["git", "diff", "--name-only", f"{base}...HEAD"],
        ["git", "diff", "--name-only", "HEAD^", "HEAD"],
    ]
    for command in commands:
        result = subprocess.run(command, text=True, capture_output=True)
        if result.returncode != 0:
            continue
        files: list[Path] = []
        for raw in result.stdout.splitlines():
            path = Path(raw)
            if (
                path.suffix == ".lean"
                and (raw == "MGAP4D.lean" or raw.startswith("MGAP4D/"))
                and path not in AGGREGATE_ROOTS
            ):
                files.append(path)
        return sorted(set(files))
    raise RuntimeError(f"cannot compute changed files from {base!r} or HEAD^")


def module_source(module: str) -> Path:
    return Path(module.replace(".", "/") + ".lean")


def output_path(source: Path) -> Path:
    return BUILD_LIB / source.with_suffix(".olean")


def direct_local_imports(source: Path) -> list[Path]:
    imports: list[Path] = []
    for line in source.read_text(encoding="utf-8").splitlines():
        match = IMPORT_RE.match(line)
        if match is None:
            continue
        module = match.group(1)
        if not module.startswith("MGAP4D"):
            continue
        dependency = module_source(module)
        if dependency.is_file() and dependency not in AGGREGATE_ROOTS:
            imports.append(dependency)
    return imports


def diagnostic_path() -> Path:
    runner_temp = Path(os.environ.get("RUNNER_TEMP", "/tmp"))
    return runner_temp / "lean-fast.log"


def compile_source(source: Path) -> None:
    output = output_path(source)
    output.parent.mkdir(parents=True, exist_ok=True)
    command = [
        "lake",
        "env",
        "lean",
        "-DautoImplicit=false",
        "-o",
        str(output),
        str(source),
    ]
    print(f"[fast] materialize direct local Lean import: {source}", flush=True)
    result = subprocess.run(command, text=True, capture_output=True)
    combined = result.stdout + result.stderr
    if combined:
        print(combined, end="", flush=True)
    diagnostic_path().write_text(
        f"$ {' '.join(command)}\n{combined}", encoding="utf-8"
    )
    if result.returncode != 0:
        raise subprocess.CalledProcessError(result.returncode, command)


def main() -> int:
    base = sys.argv[1] if len(sys.argv) > 1 else "origin/main"
    targets = changed_lean_files(base)
    changed = set(targets)
    dependencies = sorted(
        {
            dependency
            for target in targets
            for dependency in direct_local_imports(target)
            if dependency not in changed and not output_path(dependency).is_file()
        }
    )
    if not dependencies:
        print("[fast] no missing direct local Lean imports")
        return 0
    for dependency in dependencies:
        compile_source(dependency)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
