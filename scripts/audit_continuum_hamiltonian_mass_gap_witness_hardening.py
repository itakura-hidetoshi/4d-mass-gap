#!/usr/bin/env python3
"""Audit the continuum Hamiltonian mass-gap witness hardening surface."""

from __future__ import annotations

from pathlib import Path
import re
import sys

STRING_RE = re.compile(r'"(?:[^"\\]|\\.)*"')
FORBIDDEN_TOKENS_RE = re.compile(r"\b(sorry|admit|axiom|constant)\b")
TARGET_PATH = Path("MGAP4D/MathlibAnalytic/ContinuumHamiltonianMassGapWitnessHardening.lean")
THEOREM_PATH = Path("MGAP4D/MathlibAnalytic/ContinuumHamiltonianMassGapTheorem.lean")
ROOT_PATH = Path("MGAP4D/MathlibAnalytic.lean")
DOC_PATH = Path("docs/continuum_hamiltonian_mass_gap_witness_hardening.md")

REQUIRED_TARGET_ANCHORS = (
    "continuum_hamiltonian_mass_gap_witness_hardened_bundle",
    "continuum_hamiltonian_physical_witness_from_hardened_bundle",
    "continuum_hamiltonian_hphys_from_ym_witness_from_hardened_bundle",
    "continuum_hamiltonian_exact_positive_mass_gap_from_hardened_bundle",
    "continuum_hamiltonian_installed_witness_ready_from_hardened_bundle",
    "continuumYangMillsLaneHardeningData.concreteYMHardened",
    "continuumYangMillsLaneHardeningData.hphysBuiltFromYMHardened",
    "plaquetteSpectralWeightLaneHardeningData.compactSupportHardened",
    "plaquetteSpectralWeightLaneHardeningData.positiveWeightHardened",
    "continuumHamiltonianMassGapWitnessData.ready",
    "exactGapValueReal = (33 : ℝ) / 20",
    "0 < exactGapValueReal",
    "continuum_yang_mills_lane_hardening_ready",
    "plaquette_spectral_weight_lane_hardening_ready",
    "continuum_hamiltonian_mass_gap_witness_ready",
)

REQUIRED_THEOREM_ANCHORS = (
    "import MGAP4D.MathlibAnalytic.ContinuumHamiltonianMassGapWitnessHardening",
    "continuum_hamiltonian_theorem_uses_hardened_witness_bundle",
    "continuum_hamiltonian_installed_witness_ready_from_hardened_bundle",
    "continuum_hamiltonian_physical_witness_from_hardened_bundle",
    "continuum_hamiltonian_hphys_from_ym_witness_from_hardened_bundle",
    "continuum_hamiltonian_exact_positive_mass_gap_from_hardened_bundle",
    "plaquette_weight_compact_support_hardened",
    "plaquette_weight_positive_weight_hardened",
)

REQUIRED_ROOT_ANCHORS = (
    "import MGAP4D.MathlibAnalytic.ContinuumHamiltonianMassGapWitnessHardening",
)

REQUIRED_DOC_ANCHORS = (
    "Continuum Hamiltonian Mass-Gap Witness Hardening",
    "continuum_hamiltonian_mass_gap_witness_hardened_bundle",
    "continuum_hamiltonian_theorem_uses_hardened_witness_bundle",
    "continuumYangMillsLaneHardeningData.ready",
    "plaquetteSpectralWeightLaneHardeningData.ready",
    "continuumHamiltonianMassGapWitnessData.ready",
    "exactGapValueReal = (33 : ℝ) / 20",
    "0 < exactGapValueReal",
    "external audit boundary",
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
        return [f"missing continuum Hamiltonian witness hardening file for forbidden-token audit: {path}"]
    source = cleaned_lean_source(path)
    hits: list[str] = []
    for lineno, line in enumerate(source.splitlines(), start=1):
        if FORBIDDEN_TOKENS_RE.search(line):
            hits.append(f"{path}:{lineno}: forbidden token in continuum Hamiltonian witness hardening audit")
    return hits


def main() -> None:
    failures: list[str] = []
    failures.extend(audit_forbidden_tokens(TARGET_PATH))
    failures.extend(require(TARGET_PATH, REQUIRED_TARGET_ANCHORS, "continuum Hamiltonian witness hardening target", clean_lean=True))
    failures.extend(require(THEOREM_PATH, REQUIRED_THEOREM_ANCHORS, "continuum Hamiltonian theorem bridge", clean_lean=True))
    failures.extend(require(ROOT_PATH, REQUIRED_ROOT_ANCHORS, "root import", clean_lean=True))
    failures.extend(require(DOC_PATH, REQUIRED_DOC_ANCHORS, "continuum Hamiltonian witness hardening documentation", clean_lean=False))

    print("Continuum Hamiltonian mass-gap witness hardening audit")
    print(f"Hardening anchors audited: {len(REQUIRED_TARGET_ANCHORS)}")
    print(f"Theorem bridge anchors audited: {len(REQUIRED_THEOREM_ANCHORS)}")
    print("Root import audited: MGAP4D/MathlibAnalytic.lean")
    print("Documentation audited: docs/continuum_hamiltonian_mass_gap_witness_hardening.md")
    print("Forbidden Lean tokens audited: sorry/admit/axiom/constant")

    if failures:
        print("Continuum Hamiltonian mass-gap witness hardening audit failed:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        raise SystemExit(1)

    print("Continuum Hamiltonian mass-gap witness hardening audit passed")


if __name__ == "__main__":
    main()
