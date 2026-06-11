#!/usr/bin/env python3
"""Audit the spectral theorem / PVM / Hamiltonian gap-necessity boundary."""

from __future__ import annotations

from pathlib import Path
import re
import sys

STRING_RE = re.compile(r'"(?:[^"\\]|\\.)*"')
FORBIDDEN_TOKENS_RE = re.compile(r"\b(sorry|admit|axiom|constant)\b")

LEAN_PATH = Path("MGAP4D/MathlibAnalytic/SpectralPVMHamiltonianGapNecessity.lean")
ROOT_PATH = Path("MGAP4D/MathlibAnalytic.lean")
DOC_PATH = Path("docs/spectral_pvm_hamiltonian_gap_necessity.md")
CHECK_PATH = Path("scripts/check.sh")

REQUIRED_LEAN_IMPORTS = ("import MGAP4D.MathlibAnalytic.ExternalAuditReadinessGate",)

REQUIRED_LEAN_ANCHORS = (
    "SpectralPVMHamiltonianGapNecessity",
    "spectral_pvm_hamiltonian_gap_necessity_ready",
    "spectral_pvm_hamiltonian_exact_gap_eq_derived_value",
    "spectral_pvm_hamiltonian_infimum_value_eq_derived",
    "spectral_pvm_hamiltonian_attained_value_eq_derived",
    "spectral_pvm_hamiltonian_observable_atom_eq_derived",
    "spectral_pvm_hamiltonian_requires_r6_value_pinning",
    "YangMillsHamiltonianSpectralPVMAnalysisRequiresR6ValuePinning",
    "spectral_pvm_hamiltonian_positive_nonzero_mass",
    "spectral_pvm_hamiltonian_boundary_held",
    "yang_mills_hamiltonian_exact_gap_eq_spectral_value",
    "external_audit_readiness_pvm_spectral_atom_public_audit_projection",
    "external_audit_readiness_continuum_hamiltonian_chain_index_addendum_ready",
    "0 < spectralMassRealSurface.mass",
    "spectralMassRealSurface.mass ≠ 0",
    "finalTheoremReleaseSkeletonReviewSurface.externalConsensusNotClaimed",
    "publicBoundaryHeld",
    "finalReleaseHeld",
)

FORBIDDEN_STALE_ANCHORS = (
    "spectral_pvm_hamiltonian_derived_value_eq_33_over_20",
    "spectral_pvm_hamiltonian_infimum_value_eq_33_over_20",
    "spectral_pvm_hamiltonian_attained_value_eq_33_over_20",
    "spectral_pvm_hamiltonian_observable_atom_eq_33_over_20",
    "physical_continuum_hamiltonian_exact_gap_33_over_20",
)

REQUIRED_ROOT_ANCHORS = ("import MGAP4D.MathlibAnalytic.SpectralPVMHamiltonianGapNecessity",)
REQUIRED_DOC_ANCHORS = (
    "Spectral theorem / PVM / Hamiltonian gap necessity",
    "SpectralPVMHamiltonianGapNecessity",
)
REQUIRED_CHECK_ANCHORS = (
    "audit spectral theorem / PVM / Hamiltonian gap necessity",
    "python3 scripts/audit_spectral_pvm_hamiltonian_gap_necessity.py",
    "lake build MGAP4D.MathlibAnalytic.SpectralPVMHamiltonianGapNecessity",
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


def clean_lean(text: str) -> str:
    return STRING_RE.sub('""', strip_lean_comments(text))


def read(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"missing required file: {path}")
    return path.read_text(encoding="utf-8")


def require_all(text: str, anchors: tuple[str, ...], label: str, path: Path) -> list[str]:
    return [f"missing {label} anchor {anchor!r} in {path}" for anchor in anchors if anchor not in text]


def forbid_all(text: str, anchors: tuple[str, ...], label: str, path: Path) -> list[str]:
    return [f"forbidden stale {label} anchor {anchor!r} in {path}" for anchor in anchors if anchor in text]


def main() -> None:
    failures: list[str] = []
    try:
        lean_text = read(LEAN_PATH)
        lean_src = clean_lean(lean_text)
    except FileNotFoundError as exc:
        failures.append(str(exc))
        lean_src = ""

    forbidden = sorted(set(FORBIDDEN_TOKENS_RE.findall(lean_src)))
    if forbidden:
        failures.append(f"forbidden Lean tokens found in {LEAN_PATH}: {', '.join(forbidden)}")

    for path, anchors, label, clean in (
        (LEAN_PATH, REQUIRED_LEAN_IMPORTS, "Lean import", False),
        (LEAN_PATH, REQUIRED_LEAN_ANCHORS, "Lean necessity", True),
        (ROOT_PATH, REQUIRED_ROOT_ANCHORS, "root import", False),
        (DOC_PATH, REQUIRED_DOC_ANCHORS, "documentation", False),
        (CHECK_PATH, REQUIRED_CHECK_ANCHORS, "check route", False),
    ):
        try:
            text = read(path)
        except FileNotFoundError as exc:
            failures.append(str(exc))
            continue
        failures.extend(require_all(clean_lean(text) if clean else text, anchors, label, path))

    failures.extend(forbid_all(lean_src, FORBIDDEN_STALE_ANCHORS, "Lean necessity", LEAN_PATH))

    print("Spectral theorem / PVM / Hamiltonian gap necessity boundary audit")
    print(f"Lean anchors audited: {len(REQUIRED_LEAN_ANCHORS)}")
    print("Forbidden Lean tokens audited: sorry/admit/axiom/constant")

    if failures:
        print("Spectral theorem / PVM / Hamiltonian gap necessity audit failed:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        raise SystemExit(1)

    print("Spectral theorem / PVM / Hamiltonian gap necessity boundary audit passed")


if __name__ == "__main__":
    main()
