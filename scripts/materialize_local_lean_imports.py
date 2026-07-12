#!/usr/bin/env python3
"""Materialize missing local Lean import artifacts before changed-file checks.

The fast lane normally elaborates only changed leaf modules.  A newly merged
local module may be absent from the restored Lake cache, causing direct
elaboration to fall back to a much larger transitive build.  This helper walks
only the local MGAP4D import closure needed by changed files and emits missing
`.olean` files in dependency order.
"""

from __future__ import annotations

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
        if result.returncode == 0:
            files = []
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


def local_imports(source: Path) -> list[Path]:
    imports: list[Path] = []
    for line in source.read_text(encoding="utf-8").splitlines():
        match = IMPORT_RE.match(line)
        if not match:
            continue
        module = match.group(1)
        if not module.startswith("MGAP4D"):
            continue
        dependency = module_source(module)
        if dependency.is_file() and dependency not in AGGREGATE_ROOTS:
            imports.append(dependency)
    return imports


def dependency_order(targets: list[Path]) -> list[Path]:
    changed = set(targets)
    permanent: set[Path] = set()
    temporary: set[Path] = set()
    ordered: list[Path] = []

    def visit(source: Path, force: bool = False) -> None:
        if source in permanent:
            return
        if source in temporary:
            raise RuntimeError(f"local Lean import cycle at {source}")
        if not source.is_file():
            raise FileNotFoundError(source)

        must_build = force or source in changed or not output_path(source).is_file()
        if not must_build:
            permanent.add(source)
            return

        temporary.add(source)
        for dependency in local_imports(source):
            visit(dependency)
        temporary.remove(source)
        permanent.add(source)
        ordered.append(source)

    for target in targets:
        visit(target, force=True)
    return ordered


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
    print(f"[fast] materialize local Lean artifact: {source}", flush=True)
    subprocess.run(command, check=True)


def main() -> int:
    base = sys.argv[1] if len(sys.argv) > 1 else "origin/main"
    targets = changed_lean_files(base)
    if not targets:
        print("[fast] no changed Lean leaf modules to materialize")
        return 0
    ordered = dependency_order(targets)
    print("[fast] local Lean materialization order:")
    for source in ordered:
        print(f"  {source}")
    for source in ordered:
        compile_source(source)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
