#!/usr/bin/env python3
"""Audit Yang--Mills Hamiltonian spectral-derivation claim anchors.

This is a syntactic/contract audit. Lean kernel checking remains `lake build`.
The audit ensures the spectral surface is present, imported, documented,
boundary-preserving, and now exposes an explicit theorem-level Yang--Mills
Hamiltonian spectral derivation claim without baking an independent numeric value
into the upstream carrier fields.
"""

from __future__ import annotations

from pathlib import Path
import re
import sys

STRING_RE = re.compile(r'"(?:[^"\\]|\\.)*"')
FORBIDDEN_TOKENS_RE = re.compile(r"\b(sorry|admit|axiom|constant)\b")

LEAN_PATH = Path("MGAP4D/MathlibAnalytic/YangMillsHamiltonianSpectralDerivation3320.lean")
ROOT_IMPORT_PATH = Path("MGAP4D/MathlibAnalytic.lean")
DOC_PATH = Path("docs/yang_mills_hamiltonian_spectral_derivation_3320.md")
CHECK_PATH = Path("scripts/check.sh")

REQUIRED_IMPORTS = (
    "import MGAP4D.MathlibAnalytic.ContinuumHamiltonianMassGapTheorem",
    "import MGAP4D.MathlibAnalytic.SpectralMassReal",
)

REQUIRED_LEAN_ANCHORS = (
    "YangMillsHamiltonianSpectralDerivation3320",
    "yangMillsHamiltonianSpectralDerivation3320",
    "YangMillsHamiltonianSpectralDerivation3320.ready",
    "continuumHamiltonianReady",
    "hphysFromYangMills",
    "selfAdjointSpectralChainReady",
    "rayleighLowerBoundReady",
    "rayleighAttainmentReady",
    "positiveSpectralMassReady",
    "spectralInfimumValue",
    "attainedSpectralValue",
    "observableSpectralAtomValue",
    "derivedHamiltonianSpectralValue",
    "infimum_eq_derived",
    "attainment_eq_derived",
    "atom_eq_derived",
    "exactNormalizedGapDerivedFromSpectrum",
    "continuum_hamiltonian_exact_gap_value_preserved",
    "YangMillsHamiltonianPhysicalSpectrumIdentifiesExactGapValue",
    "yang_mills_hamiltonian_physical_spectrum_identifies_exact_gap_value",
    "yang_mills_hamiltonian_exact_gap_value_from_physical_spectrum",
    "yang_mills_hamiltonian_spectral_derivation_3320_ready",
    "yang_mills_hamiltonian_spectral_infimum_eq_derived",
    "yang_mills_hamiltonian_spectral_attainment_eq_derived",
    "yang_mills_hamiltonian_observable_atom_eq_derived",
    "yang_mills_hamiltonian_exact_gap_eq_spectral_value",
    "yang_mills_hamiltonian_spectral_derivation_positive_mass",
    "yang_mills_hamiltonian_spectral_derivation_nonzero_mass",
    "yang_mills_hamiltonian_spectral_derivation_public_boundary_held",
    "yang_mills_hamiltonian_spectral_derivation_final_release_held",
)

REQUIRED_SPECTRAL_CHAIN_ANCHORS = (
    "rayleighLowerBoundRealSurface.ready",
    "rayleighAttainmentRealSurface.ready",
    "spectralMassRealSurface.ready",
    "D.spectralInfimumValue = D.derivedHamiltonianSpectralValue",
    "D.attainedSpectralValue = D.derivedHamiltonianSpectralValue",
    "D.observableSpectralAtomValue = D.derivedHamiltonianSpectralValue",
    "exactGapValueReal = D.derivedHamiltonianSpectralValue",
    "0 < spectralMassRealSurface.mass",
    "spectralMassRealSurface.mass ≠ 0",
)

REQUIRED_CLAIM_ANCHORS = (
    "YangMillsHamiltonianSpectralDerivationClaim3320",
    "yang_mills_hamiltonian_spectral_derivation_claim_3320",
    "yang_mills_hamiltonian_spectral_derivation_claim_forces_gap_33_over_20",
    "yang_mills_hamiltonian_spectral_derivation_claim_positive_nonzero_pvm_mass",
    "yang_mills_hamiltonian_spectral_derivation_claim_boundary_held",
    "yang_mills_hamiltonian_spectral_pvm_analysis_forces_gap_33_over_20",
    "yang_mills_hamiltonian_spectral_theorem_pvm_hamiltonian_analysis_forces_exact_gap",
    "yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue =\n    (33 : ℝ) / 20",
    "yangMillsHamiltonianSpectralDerivation3320.theoremWitnessOnly",
    "yangMillsHamiltonianSpectralDerivation3320.noExternalConsensusClaim",
)

FORBIDDEN_UPSTREAM_NUMERIC_ANCHORS = (
    "spectralInfimumValue_eq_3320",
    "attainedSpectralValue_eq_3320",
    "observableSpectralAtomValue_eq_3320",
    "derivedHamiltonianSpectralValue_eq_3320",
    "yang_mills_hamiltonian_spectral_infimum_eq_3320",
    "yang_mills_hamiltonian_spectral_attainment_eq_3320",
    "yang_mills_hamiltonian_observable_atom_eq_3320",
    "yang_mills_hamiltonian_spectral_analysis_derives_3320",
    "yang_mills_hamiltonian_spectral_derivation_exact_gap_value",
    "exactNormalizedGapDerivedFromSpectrum := rfl",
    "D.spectralInfimumValue = (33 : ℝ) / 20",
    "D.attainedSpectralValue = (33 : ℝ) / 20",
    "D.observableSpectralAtomValue = (33 : ℝ) / 20",
    "D.derivedHamiltonianSpectralValue = (33 : ℝ) / 20",
)

REQUIRED_ROOT_IMPORTS = (
    "import MGAP4D.MathlibAnalytic.YangMillsHamiltonianSpectralDerivation3320",
)

REQUIRED_DOC_ANCHORS = (
    "Yang--Mills Hamiltonian spectral derivation claim",
    "no upstream 33/20 claim",
    "R6 exact atom layer",
    "physical spectrum identifies exact gap carrier",
    "YangMillsHamiltonianPhysicalSpectrumIdentifiesExactGapValue",
    "yang_mills_hamiltonian_physical_spectrum_identifies_exact_gap_value",
    "yang_mills_hamiltonian_exact_gap_value_from_physical_spectrum",
    "continuum_hamiltonian_exact_gap_value_preserved",
    "spectral infimum value = derived Hamiltonian spectral value",
    "attained spectral value = derived Hamiltonian spectral value",
    "observable spectral atom value = derived Hamiltonian spectral value",
    "yang_mills_hamiltonian_spectral_infimum_eq_derived",
    "yang_mills_hamiltonian_spectral_attainment_eq_derived",
    "yang_mills_hamiltonian_observable_atom_eq_derived",
    "yang_mills_hamiltonian_exact_gap_eq_spectral_value",
    "YangMillsHamiltonianSpectralDerivationClaim3320",
    "yang_mills_hamiltonian_spectral_derivation_claim_3320",
    "yang_mills_hamiltonian_spectral_derivation_claim_forces_gap_33_over_20",
    "yang_mills_hamiltonian_spectral_derivation_claim_positive_nonzero_pvm_mass",
    "yang_mills_hamiltonian_spectral_derivation_claim_boundary_held",
    "Yang--Mills Hamiltonian spectral derivation claim",
    "PVM spectral mass > 0",
    "noExternalConsensusClaim",
    "yang_mills_hamiltonian_spectral_derivation_public_boundary_held",
)

REQUIRED_CHECK_ANCHORS = (
    "audit Yang-Mills Hamiltonian spectral value alignment before R6",
    "scripts/audit_yang_mills_hamiltonian_spectral_derivation_3320.py",
    "build Yang-Mills Hamiltonian spectral value alignment before R6",
    "lake build MGAP4D.MathlibAnalytic.YangMillsHamiltonianSpectralDerivation3320",
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
        i += 1
    return "".join(out)


def strip_strings(text: str) -> str:
    return STRING_RE.sub('""', text)


def lean_code(text: str) -> str:
    return strip_strings(strip_lean_comments(text))


def require_file(path: Path) -> str:
    if not path.exists():
        raise AssertionError(f"missing required file: {path}")
    return path.read_text(encoding="utf-8")


def require_all(label: str, text: str, anchors: tuple[str, ...]) -> None:
    missing = [anchor for anchor in anchors if anchor not in text]
    if missing:
        raise AssertionError(f"{label} missing anchors: {', '.join(missing)}")


def forbid_all(label: str, text: str, anchors: tuple[str, ...]) -> None:
    present = [anchor for anchor in anchors if anchor in text]
    if present:
        raise AssertionError(f"{label} forbidden stale anchors present: {', '.join(present)}")


def main() -> int:
    lean_text = require_file(LEAN_PATH)
    lean_without_comments = strip_lean_comments(lean_text)
    lean_src = lean_code(lean_text)

    forbidden = sorted(set(FORBIDDEN_TOKENS_RE.findall(lean_src)))
    if forbidden:
        raise AssertionError(f"forbidden Lean tokens found in {LEAN_PATH}: {', '.join(forbidden)}")

    require_all("Lean imports", lean_without_comments, REQUIRED_IMPORTS)
    require_all("Lean anchors", lean_without_comments, REQUIRED_LEAN_ANCHORS)
    require_all("spectral chain anchors", lean_without_comments, REQUIRED_SPECTRAL_CHAIN_ANCHORS)
    require_all("Yang-Mills spectral derivation claim anchors", lean_without_comments, REQUIRED_CLAIM_ANCHORS)
    forbid_all("Lean upstream numeric anchors", lean_without_comments, FORBIDDEN_UPSTREAM_NUMERIC_ANCHORS)

    root_text = require_file(ROOT_IMPORT_PATH)
    require_all("root import", root_text, REQUIRED_ROOT_IMPORTS)

    doc_text = require_file(DOC_PATH)
    require_all("documentation", doc_text, REQUIRED_DOC_ANCHORS)

    check_text = require_file(CHECK_PATH)
    require_all("check.sh", check_text, REQUIRED_CHECK_ANCHORS)

    print("Yang-Mills Hamiltonian spectral derivation claim audit")
    print(f"Lean anchors audited: {len(REQUIRED_LEAN_ANCHORS)}")
    print(f"Spectral-chain anchors audited: {len(REQUIRED_SPECTRAL_CHAIN_ANCHORS)}")
    print(f"Claim anchors audited: {len(REQUIRED_CLAIM_ANCHORS)}")
    print(f"Forbidden stale upstream numeric anchors audited: {len(FORBIDDEN_UPSTREAM_NUMERIC_ANCHORS)}")
    print(f"Root import audited: {ROOT_IMPORT_PATH}")
    print(f"Documentation audited: {DOC_PATH}")
    print("Forbidden Lean tokens audited: sorry/admit/axiom/constant")
    print("Yang-Mills Hamiltonian spectral derivation claim audit passed")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except AssertionError as exc:
        print(f"audit_yang_mills_hamiltonian_spectral_derivation_3320.py: {exc}", file=sys.stderr)
        raise SystemExit(1)
