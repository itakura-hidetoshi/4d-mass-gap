#!/usr/bin/env python3
"""Audit the external audit theorem witness index and its certificate."""

from __future__ import annotations

from pathlib import Path
import sys

DOC_PATH = Path("docs/external_audit_theorem_witness_index.md")
CHECK_PATH = Path("scripts/check.sh")
ROOT_PATH = Path("MGAP4D/MathlibAnalytic.lean")
INDEX_PATH = Path("MGAP4D/MathlibAnalytic/ExternalAuditTheoremWitnessIndex.lean")
WITNESS_PATH = Path("MGAP4D/MathlibAnalytic/ContinuumHamiltonianMassGapWitness.lean")
THEOREM_PATH = Path("MGAP4D/MathlibAnalytic/ContinuumHamiltonianMassGapTheorem.lean")
ADOPTION_PATH = Path("MGAP4D/MathlibAnalytic/ContinuumHamiltonianMassGapReleaseAdoption.lean")

REQUIRED_DOC_ANCHORS = (
    "External audit theorem witness index certificate",
    "Pull request: 20",
    "Workflow run: 25978245953",
    "Workflow job: 76362202736",
    "Merge checkpoint: 15379002b160c944f311e2013b8b8d1d174d6c67",
    "Head checkpoint: 89c97b8ca3a770a0525ea16591f21951fd1828e2",
    "Build completed successfully (8372 jobs).",
    "Lean files scanned: 461",
    "sorry: 0",
    "admit: 0",
    "axiom: 0",
    "constant: 0",
    "lean_files: 461",
    "imports: 1203",
    "declaration_like_lines: 2697",
    "total_lines: 28031",
    "MGAP4D.MathlibAnalytic.ExternalAuditTheoremWitnessIndex",
    "ExternalAuditTheoremWitnessIndexData",
    "externalAuditTheoremWitnessIndexData",
    "exactGapValueReal = (33 : ℝ) / 20",
    "continuumHamiltonianMassGapWitnessData.continuumHamiltonianToMassGapChainReady",
    "continuumHamiltonianMassGapWitnessData.noExternalConsensusClaim",
)

REQUIRED_INDEX_THEOREMS = (
    "external_audit_theorem_witness_index_ready",
    "external_audit_theorem_witness_index_positive_exact_mass_gap",
    "external_audit_theorem_witness_index_chain_ready",
    "external_audit_theorem_witness_index_no_external_consensus_claim",
    "external_audit_theorem_witness_index_boundaries_held",
)

REQUIRED_INDEX_FIELD_ANCHORS = (
    "externalAuditGateReady : externalAuditReadinessGateData.ready",
    "releaseAdoptionReady :",
    "positiveExactMassGapReady :",
    "continuumHamiltonianChainReady :",
    "theoremWitnessOnly : continuumHamiltonianMassGapWitnessData.theoremWitnessOnly",
    "externalConsensusNotClaimed :",
    "publicBoundaryHeld : continuumHamiltonianMassGapWitnessData.publicBoundaryHeld",
    "finalReleaseHeld : continuumHamiltonianMassGapWitnessData.finalReleaseHeld",
)

REQUIRED_CONTINUUM_ROUTE_ANCHORS = (
    "ContinuumHamiltonianMassGapWitness",
    "ContinuumHamiltonianMassGapTheorem",
    "ContinuumHamiltonianMassGapReleaseAdoption",
    "continuumHamiltonianMassGapWitnessData.ready",
    "continuum_hamiltonian_mass_gap_witness_ready",
    "continuum_hamiltonian_mass_gap_theorem_ready",
    "continuum_hamiltonian_mass_gap_release_adoption_ready",
    "continuum_hamiltonian_derives_mass_gap_chain",
)

REQUIRED_BOUNDARY_PHRASES = (
    "external audit completed",
    "external mathematical consensus obtained",
    "final theorem release opened",
    "future residuals impossible",
    "public theorem boundary removed",
    "Clay problem accepted as solved",
    "Lean semantics changed: no",
    "External consensus claimed: no",
    "External audit completed: no",
    "Final theorem release opened: no",
)

REQUIRED_CHECK_ROUTE_ANCHORS = (
    "python3 scripts/audit_external_audit_theorem_witness_index.py",
    "lake build MGAP4D.MathlibAnalytic.ExternalAuditTheoremWitnessIndex",
    "lake build",
)

REQUIRED_ROOT_ANCHORS = (
    "import MGAP4D.MathlibAnalytic.ContinuumHamiltonianMassGapWitness",
    "import MGAP4D.MathlibAnalytic.ContinuumHamiltonianMassGapTheorem",
    "import MGAP4D.MathlibAnalytic.ContinuumHamiltonianMassGapReleaseAdoption",
    "import MGAP4D.MathlibAnalytic.ExternalAuditTheoremWitnessIndex",
)


def read(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"missing required file: {path}")
    return path.read_text(encoding="utf-8")


def require_all(text: str, anchors: tuple[str, ...], label: str, path: Path) -> list[str]:
    return [f"missing {label} anchor {anchor!r} in {path}" for anchor in anchors if anchor not in text]


def main() -> None:
    failures: list[str] = []

    paths = (DOC_PATH, CHECK_PATH, ROOT_PATH, INDEX_PATH, WITNESS_PATH, THEOREM_PATH, ADOPTION_PATH)
    contents: dict[Path, str] = {}
    for path in paths:
        try:
            contents[path] = read(path)
        except FileNotFoundError as exc:
            failures.append(str(exc))
            contents[path] = ""

    doc = contents[DOC_PATH]
    check = contents[CHECK_PATH]
    root = contents[ROOT_PATH]
    index = contents[INDEX_PATH]
    witness = contents[WITNESS_PATH]
    theorem = contents[THEOREM_PATH]
    adoption = contents[ADOPTION_PATH]
    continuum_bundle = "\n".join((witness, theorem, adoption, index, doc))

    failures.extend(require_all(doc, REQUIRED_DOC_ANCHORS, "doc", DOC_PATH))
    failures.extend(require_all(doc, REQUIRED_INDEX_THEOREMS, "index-theorem", DOC_PATH))
    failures.extend(require_all(doc, REQUIRED_CONTINUUM_ROUTE_ANCHORS, "continuum-route", DOC_PATH))
    failures.extend(require_all(doc, REQUIRED_BOUNDARY_PHRASES, "boundary", DOC_PATH))
    failures.extend(require_all(index, REQUIRED_INDEX_THEOREMS, "index-theorem", INDEX_PATH))
    failures.extend(require_all(index, REQUIRED_INDEX_FIELD_ANCHORS, "index-field", INDEX_PATH))
    failures.extend(require_all(continuum_bundle, REQUIRED_CONTINUUM_ROUTE_ANCHORS, "continuum-route", INDEX_PATH))
    failures.extend(require_all(check, REQUIRED_CHECK_ROUTE_ANCHORS, "check-route", CHECK_PATH))
    failures.extend(require_all(root, REQUIRED_ROOT_ANCHORS, "root-import", ROOT_PATH))

    print("External audit theorem witness index audit")
    print(f"Documentation anchors audited: {len(REQUIRED_DOC_ANCHORS)}")
    print(f"Index theorem anchors audited: {len(REQUIRED_INDEX_THEOREMS)}")
    print(f"Index field anchors audited: {len(REQUIRED_INDEX_FIELD_ANCHORS)}")
    print(f"Continuum route anchors audited: {len(REQUIRED_CONTINUUM_ROUTE_ANCHORS)}")
    print("Boundary phrases audited: external audit / consensus / final-release boundaries")
    print(f"Documentation audited: {DOC_PATH}")
    print(f"Lean index audited: {INDEX_PATH}")

    if failures:
        print("External audit theorem witness index audit failed:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        raise SystemExit(1)

    print("External audit theorem witness index audit passed")


if __name__ == "__main__":
    main()
