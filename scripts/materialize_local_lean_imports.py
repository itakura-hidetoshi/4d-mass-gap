#!/usr/bin/env python3
"""Materialize the recent local Lean frontier needed by changed leaf files.

The restored cache predates several consecutive PVM and functional-calculus PRs.
Recursing through the entire repository import graph exceeds the fast-check
budget, so this helper compiles only the known recent frontier, in dependency
order, and then lets the normal changed-file check elaborate the changed leaf.
Compiler diagnostics are mirrored to the standard fast-check artifact path.
"""

from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path

ROOT = Path.cwd()
BUILD_LIB = ROOT / ".lake" / "build" / "lib" / "lean"

RECENT_FRONTIER = [
    Path("MGAP4D/MathlibAnalytic/WightmanOSCanonicalRestrictedHamiltonianPVMResolventLocalVanish.lean"),
    Path("MGAP4D/MathlibAnalytic/WightmanOSCanonicalRestrictedHamiltonianPVMFunctionalCalculusCore.lean"),
    Path("MGAP4D/MathlibAnalytic/WightmanOSCanonicalRestrictedHamiltonianPVMLocalFunctionalCalculus.lean"),
    Path("MGAP4D/MathlibAnalytic/WightmanOSPVMDisjointCompositionDerived.lean"),
    Path("MGAP4D/MathlibAnalytic/WightmanOSPVMFiniteSimpleSpectralIntegral.lean"),
    Path("MGAP4D/MathlibAnalytic/WightmanOSPVMSimpleFuncSpectralIntegral.lean"),
    Path("MGAP4D/MathlibAnalytic/WightmanOSPVMSimpleFuncUniformCauchy.lean"),
    Path("MGAP4D/MathlibAnalytic/WightmanOSPVMBoundedBorelUniformApproximation.lean"),
]


def output_path(source: Path) -> Path:
    return BUILD_LIB / source.with_suffix(".olean")


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
    print(f"[fast] materialize recent Lean frontier: {source}", flush=True)
    result = subprocess.run(command, text=True, capture_output=True)
    combined = result.stdout + result.stderr
    if combined:
        print(combined, end="", flush=True)
    with diagnostic_path().open("a", encoding="utf-8") as log:
        log.write(f"$ {' '.join(command)}\n{combined}")
    if result.returncode != 0:
        raise subprocess.CalledProcessError(result.returncode, command)


def main() -> int:
    diagnostic_path().write_text("", encoding="utf-8")
    del sys.argv  # The base ref is intentionally irrelevant to this bounded frontier.
    compiled = False
    for source in RECENT_FRONTIER:
        if not source.is_file() or output_path(source).is_file():
            continue
        compile_source(source)
        compiled = True
    if not compiled:
        print("[fast] recent Lean frontier already materialized")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
