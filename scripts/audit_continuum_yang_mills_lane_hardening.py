#!/usr/bin/env python3
"""Audit the continuum Yang--Mills lane hardening layer."""

from __future__ import annotations

from pathlib import Path
import re
import sys

STRING_RE = re.compile(r'"(?:[^"\\]|\\.)*"')
FORBIDDEN_TOKENS_RE = re.compile(r"\b(sorry|admit|axiom|constant)\b")
TARGET_PATH = Path("MGAP4D/MathlibAnalytic/ContinuumYangMillsLaneHardening.lean")
ROOT_PATH = Path("MGAP4D/MathlibAnalytic.lean")
DOC_PATH = Path("docs/continuum_yang_mills_lane_hardening.md")

REQUIRED_TARGET_ANCHORS = (
    "ContinuumYangMillsLaneHardeningData",
    "ContinuumYangMillsLaneHardeningData.ready",
    "continuumYangMillsLaneHardeningData",
    "continuum_yang_mills_lane_hardening_ready",
    "selfAdjointLaneReady",
    "concreteYMSkeletonReady",
    "spectralSkeletonReady",
    "continuumSpectralReady",
    "normalizationBridgeReady",
    "concreteYMHardened",
    "hphysBuiltFromYMHardened",
    "plaquetteCenteredHardened",
    "normalizationBridgeHardened",
    "spectralRealizationHardened",
    "exactAtomHardened",
    "continuumSpectralTheoremHardened",
    "continuumLimitBoundaryVisible",
    "hardPhysicalBoundaryVisible",
    "exactValuePreserved",
    "reviewLevelOnly",
    "publicBoundaryHeld",
    "finalReleaseHeld",
)

REQUIRED_THEOREM_ANCHORS = (
    "continuum_ym_concrete_skeleton_hardened",
    "continuum_ym_hphys_built_from_ym_hardened",
    "continuum_ym_plaquette_centered_hardened",
    "continuum_ym_normalization_bridge_hardened",
    "continuum_ym_spectral_realization_hardened",
    "continuum_ym_exact_atom_hardened",
    "continuum_ym_continuum_spectral_theorem_hardened",
    "continuum_ym_continuum_limit_boundary_visible",
    "continuum_ym_hard_physical_boundary_visible",
    "continuum_ym_exact_value_preserved",
)

REQUIRED_ROOT_ANCHORS = (
    "import MGAP4D.MathlibAnalytic.ContinuumYangMillsLaneHardening",
)

REQUIRED_DOC_ANCHORS = (
    "Continuum Yang-Mills Lane Hardening",
    "concreteYMHardened",
    "hphysBuiltFromYMHardened",
    "plaquetteCenteredHardened",
    "normalizationBridgeHardened",
    "spectralRealizationHardened",
    "exactAtomHardened",
    "continuumSpectralTheoremHardened",
    "continuumLimitBoundaryVisible",
)


def strip_lean_comments(text: str) -> str:
    out: list[str] = []
    i = 0
    depth = 0
    while i < len(text):
        if depth == 0 and text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                i += 1
            if i < len(text):
                out.append("\n")
                i += 1
            continue
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth > 0 and text.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if depth == 0:
            out.append(text[i])
        elif text[i] == "\n":
            out.append("\n")
        i += 1
    return "".join(out)


def cleaned_lean_source(path: Path) -> str:
    return STRING_RE.sub('""', strip_lean_comments(path.read_text(encoding="utf-8")))


def require(path: Path, anchors: tuple[str, ...], label: str, *, clean_lean: bool) -> list[str]:
    if not path.exists():
        return [f"missing {label} file: {path}"]
    source = cleaned_lean_source(path) if clean_lean else path.read_text(encoding="utf-8")
    return [f"missing {label} anchor {anchor!r} in {path}" for anchor in anchors if anchor not in source]


def audit_forbidden_tokens(path: Path) -> list[str]:
    if not path.exists():
        return [f"missing continuum YM hardening file for forbidden-token audit: {path}"]
    source = cleaned_lean_source(path)
    hits: list[str] = []
    for lineno, line in enumerate(source.splitlines(), start=1):
        if FORBIDDEN_TOKENS_RE.search(line):
            hits.append(f"{path}:{lineno}: forbidden token in continuum YM audit")
    return hits


def main() -> None:
    failures: list[str] = []
    failures.extend(audit_forbidden_tokens(TARGET_PATH))
    failures.extend(require(TARGET_PATH, REQUIRED_TARGET_ANCHORS, "continuum YM target", clean_lean=True))
    failures.extend(require(TARGET_PATH, REQUIRED_THEOREM_ANCHORS, "continuum YM theorem", clean_lean=True))
    failures.extend(require(ROOT_PATH, REQUIRED_ROOT_ANCHORS, "root import", clean_lean=True))
    failures.extend(require(DOC_PATH, REQUIRED_DOC_ANCHORS, "continuum YM documentation", clean_lean=False))

    print("Continuum Yang-Mills lane hardening audit")
    print(f"Continuum YM anchors audited: {len(REQUIRED_TARGET_ANCHORS)}")
    print(f"Continuum YM theorem anchors audited: {len(REQUIRED_THEOREM_ANCHORS)}")
    print("Root import audited: MGAP4D/MathlibAnalytic.lean")
    print("Documentation audited: docs/continuum_yang_mills_lane_hardening.md")
    print("Forbidden Lean tokens audited: sorry/admit/axiom/constant")

    if failures:
        print("Continuum Yang-Mills lane hardening audit failed:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        raise SystemExit(1)

    print("Continuum Yang-Mills lane hardening audit passed")


if __name__ == "__main__":
    main()
