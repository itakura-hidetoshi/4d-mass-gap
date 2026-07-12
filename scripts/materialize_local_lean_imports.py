#!/usr/bin/env python3
"""Materialize a shallow local Lean import closure for changed leaf files.

The restored cache may omit the most recently merged local modules.  Walking the
entire repository closure can exceed the fast-check budget, so this helper only
walks two local import edges below each changed leaf.  This is enough to bridge
recent consecutive PR layers while leaving older dependencies to the cache.
Compiler diagnostics are mirrored to the standard fast-check artifact path.
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
MAX_IMPORT_DEPTH = 2


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
    return sorted(set(imports))


def diagnostic_path() -> Path:
    return Path(os.environ.get("RUNNER_TEMP", "/tmp")) / "lean-fast.log"


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
    print(f"[fast] materialize shallow local Lean import: {source}", flush=True)
    result = subprocess.run(command, text=True, capture_output=True)
    combined = result.stdout + result.stderr
    if combined:
        print(combined, end="", flush=True)
    with diagnostic_path().open("a", encoding="utf-8") as log:
        log.write(f"$ {' '.join(command)}\n{combined}")
    if result.returncode != 0:
        raise subprocess.CalledProcessError(result.returncode, command)


def shallow_dependency_order(targets: list[Path]) -> list[Path]:
    changed = set(targets)
    permanent: set[Path] = set()
    temporary: set[Path] = set()
    ordered: list[Path] = []

    def visit(source: Path, depth: int) -> None:
        if source in permanent or output_path(source).is_file():
            permanent.add(source)
            return
        if source in temporary:
            raise RuntimeError(f"local Lean import cycle at {source}")
        if depth > MAX_IMPORT_DEPTH:
            return
        temporary.add(source)
        if depth < MAX_IMPORT_DEPTH:
            for dependency in direct_local_imports(source):
                if dependency not in changed:
                    visit(dependency, depth + 1)
        temporary.remove(source)
        permanent.add(source)
        if source not in changed:
            ordered.append(source)

    for target in targets:
        for dependency in direct_local_imports(target):
            if dependency not in changed:
                visit(dependency, 1)
    return ordered


def main() -> int:
    diagnostic_path().write_text("", encoding="utf-8")
    base = sys.argv[1] if len(sys.argv) > 1 else "origin/main"
    targets = changed_lean_files(base)
    ordered = shallow_dependency_order(targets)
    if not ordered:
        print("[fast] no missing shallow local Lean imports")
        return 0
    print("[fast] shallow local Lean materialization order:")
    for source in ordered:
        print(f"  {source}")
    for source in ordered:
        compile_source(source)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
