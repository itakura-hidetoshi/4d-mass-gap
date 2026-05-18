#!/usr/bin/env python3
"""Audit the from-scratch concrete analytic spine.

This audit ensures the new branch starts from Mathlib-native concrete objects
instead of recycling the replay/audit-only spectral surfaces as if they were a
fully concrete physical construction.
"""

from __future__ import annotations

from pathlib import Path
import re
import sys

STRING_RE = re.compile(r'"(?:[^"\\]|\\.)*"')
FORBIDDEN_TOKENS_RE = re.compile(r"\b(sorry|admit|axiom|constant)\b")
TARGET_PATH = Path("MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineRealHilbertDomain.lean")
ROOT_PATH = Path("MGAP4D/MathlibAnalytic.lean")

REQUIRED_TARGET_ANCHORS = (
    "ConcreteRealHilbertSpace",
    "concrete_real_hilbert_space_normed_add_comm_group",
    "concrete_real_hilbert_space_inner_product_space",
    "concrete_real_hilbert_space_complete",
    "concreteRealDenseDomain",
    "concrete_real_dense_domain_dense",
    "ConcreteDenseDomainOperator",
    "concreteIdentityDenseDomainOperator",
    "concrete_identity_dense_domain_operator_domain",
    "concrete_identity_dense_domain_operator_dense",
    "ConcreteDenseDomainOperator.graph",
    "concrete_identity_dense_domain_operator_graph_nonempty",
    "ConcreteDenseDomainOperator.graphNorm",
    "concrete_dense_domain_operator_graphNorm_nonneg",
    "concrete_identity_dense_domain_operator_graphNorm_eq",
    "ConcreteGraphLimitWitness",
    "ConcreteGraphSequence",
    "ConcreteGraphSequence.graphPoint",
    "ConcreteGraphNormCauchySurface",
    "ConcreteGraphConvergenceSurface",
    "ConcreteClosableWitness",
    "ConcreteGraphClosureCandidate",
    "ConcreteClosedGraphWitness",
    "concreteIdentityGraphLimitWitness",
    "concreteIdentityGraphSequence",
    "concreteIdentityGraphNormCauchySurface",
    "concreteIdentityGraphConvergenceSurface",
    "concreteIdentityClosableWitness",
    "concreteIdentityGraphClosureCandidate",
    "concrete_identity_graph_closure_candidate_nonempty",
    "concrete_identity_graph_closure_candidate_contains_graph",
    "concrete_identity_graph_limit_point_mem_closure_candidate",
    "concreteIdentityClosedGraphWitness",
    "concrete_identity_closable_witness_closure_candidate_nonempty",
    "concrete_identity_graph_subset_closure_candidate",
    "concreteAnalyticSpineR1Ready",
    "concreteAnalyticSpineR2DomainSurfaceReady",
    "concreteAnalyticSpineR2GraphSurfaceReady",
    "concreteAnalyticSpineR2GraphSequenceSurfaceReady",
    "concreteAnalyticSpineR2ClosableSurfaceReady",
    "concreteAnalyticSpineR2GraphClosureSurfaceReady",
    "concrete_analytic_spine_r1_ready",
    "concrete_analytic_spine_r2_domain_surface_ready",
    "concrete_analytic_spine_r2_graph_surface_ready",
    "concrete_analytic_spine_r2_graph_sequence_surface_ready",
    "concrete_analytic_spine_r2_closable_surface_ready",
    "concrete_analytic_spine_r2_graph_closure_surface_ready",
    "concreteAnalyticSpineHardResidualBoundaryHeld",
    "concrete_analytic_spine_hard_residual_boundary_held",
)

REQUIRED_MATHLIB_TYPECLASS_ANCHORS = (
    "NormedAddCommGroup ConcreteRealHilbertSpace",
    "InnerProductSpace ℝ ConcreteRealHilbertSpace",
    "CompleteSpace ConcreteRealHilbertSpace",
    "Dense concreteRealDenseDomain",
    "Dense concreteIdentityDenseDomainOperator.domain",
    "Set.univ",
)

REQUIRED_GRAPH_ANCHORS = (
    "Set (ConcreteRealHilbertSpace × ConcreteRealHilbertSpace)",
    "(concreteIdentityDenseDomainOperator.graph).Nonempty",
    "T.graphNorm x",
    "0 ≤ T.graphNorm x",
    "0 ≤ concreteIdentityDenseDomainOperator.graphNorm x",
    "concreteIdentityDenseDomainOperator.graphNorm x = 2 * ‖(x.1 : ConcreteRealHilbertSpace)‖",
)

REQUIRED_GRAPH_SEQUENCE_ANCHORS = (
    "seq : ℕ → T.domain",
    "ConcreteGraphSequence.graphPoint",
    "graphSequence : ConcreteGraphSequence T",
    "graphNormCauchy : Prop",
    "candidateLimit : ConcreteGraphLimitWitness T",
    "graphPointConverges : Prop",
    "concreteIdentityGraphNormCauchySurface.graphNormCauchy",
    "concreteIdentityGraphConvergenceSurface.graphPointConverges",
)

REQUIRED_CLOSABLE_SURFACE_ANCHORS = (
    "limitPoint : ConcreteRealHilbertSpace × ConcreteRealHilbertSpace",
    "approximatedByGraph : Prop",
    "closureCandidate : Set (ConcreteRealHilbertSpace × ConcreteRealHilbertSpace)",
    "graphSubsetClosureCandidate : T.graph ⊆ closureCandidate",
    "closureCandidateNonempty : closureCandidate.Nonempty",
    "concreteIdentityClosableWitness.closureCandidate.Nonempty",
    "concreteIdentityDenseDomainOperator.graph ⊆",
)

REQUIRED_GRAPH_CLOSURE_SURFACE_ANCHORS = (
    "carrier : Set (ConcreteRealHilbertSpace × ConcreteRealHilbertSpace)",
    "containsGraph : T.graph ⊆ carrier",
    "carrierNonempty : carrier.Nonempty",
    "candidateContainsLimit : graphLimitWitness.limitPoint ∈ closureCandidate.carrier",
    "boundaryNotClosedOperatorTheorem : Prop",
    "concreteIdentityGraphClosureCandidate.carrier.Nonempty",
    "concreteIdentityDenseDomainOperator.graph ⊆\n    concreteIdentityGraphClosureCandidate.carrier",
    "concreteIdentityGraphLimitWitness.limitPoint ∈\n    concreteIdentityGraphClosureCandidate.carrier",
    "concreteIdentityClosedGraphWitness.boundaryNotClosedOperatorTheorem",
)

REQUIRED_BOUNDARY_ANCHORS = (
    "physical Hamiltonian domain",
    "not yet a claim of a physical",
    "does not assert unboundedness",
    "self-adjointness",
    "PVM",
    "physical 4D Yang--Mills Hamiltonian",
    "This is not closedness yet",
    "graph norm",
    "This is still not a closed",
    "does not assert a physical closed operator",
    "not a closed-operator theorem",
    "not self-adjointness",
    "spectral theorem",
    "does not open R3",
)

REQUIRED_ROOT_IMPORTS = (
    "import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineRealHilbertDomain",
)

FORBIDDEN_PREMATURE_CLAIMS = (
    "SelfAdjointPhysicalHamiltonianReady",
    "ConcretePVMSpectralMeasureReady",
    "NondefinitionalSpectralAtom3320Ready",
    "PositiveSpectralWeightDerivation3320Ready",
    "fully concrete physical 4D Yang--Mills Hamiltonian completed",
    "concreteAnalyticSpineClosedOperatorReady",
    "concreteAnalyticSpineSelfAdjointReady",
    "ConcreteClosedOperatorWitness",
    "ConcreteSelfAdjointWitness",
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


def forbid(path: Path, anchors: tuple[str, ...], label: str, *, clean_lean: bool) -> list[str]:
    if not path.exists():
        return []
    source = cleaned_lean_source(path) if clean_lean else path.read_text(encoding="utf-8")
    return [f"forbidden {label} phrase {anchor!r} in {path}" for anchor in anchors if anchor in source]


def audit_forbidden_tokens(path: Path) -> list[str]:
    if not path.exists():
        return [f"missing concrete analytic spine file for forbidden-token audit: {path}"]
    source = cleaned_lean_source(path)
    hits: list[str] = []
    for lineno, line in enumerate(source.splitlines(), start=1):
        if FORBIDDEN_TOKENS_RE.search(line):
            hits.append(f"{path}:{lineno}: forbidden Lean token in concrete analytic spine")
    return hits


def main() -> None:
    failures: list[str] = []
    failures.extend(audit_forbidden_tokens(TARGET_PATH))
    failures.extend(require(TARGET_PATH, REQUIRED_TARGET_ANCHORS, "concrete analytic spine target", clean_lean=True))
    failures.extend(require(TARGET_PATH, REQUIRED_MATHLIB_TYPECLASS_ANCHORS, "Mathlib typeclass", clean_lean=True))
    failures.extend(require(TARGET_PATH, REQUIRED_GRAPH_ANCHORS, "graph surface", clean_lean=True))
    failures.extend(require(TARGET_PATH, REQUIRED_GRAPH_SEQUENCE_ANCHORS, "graph sequence surface", clean_lean=True))
    failures.extend(require(TARGET_PATH, REQUIRED_CLOSABLE_SURFACE_ANCHORS, "closable surface", clean_lean=True))
    failures.extend(require(TARGET_PATH, REQUIRED_GRAPH_CLOSURE_SURFACE_ANCHORS, "graph closure surface", clean_lean=True))
    failures.extend(require(TARGET_PATH, REQUIRED_BOUNDARY_ANCHORS, "boundary", clean_lean=False))
    failures.extend(require(ROOT_PATH, REQUIRED_ROOT_IMPORTS, "root import", clean_lean=False))
    failures.extend(forbid(TARGET_PATH, FORBIDDEN_PREMATURE_CLAIMS, "premature closure", clean_lean=False))

    print("Concrete analytic spine from scratch audit")
    print(f"Target anchors audited: {len(REQUIRED_TARGET_ANCHORS)}")
    print(f"Mathlib typeclass anchors audited: {len(REQUIRED_MATHLIB_TYPECLASS_ANCHORS)}")
    print(f"Graph surface anchors audited: {len(REQUIRED_GRAPH_ANCHORS)}")
    print(f"Graph sequence anchors audited: {len(REQUIRED_GRAPH_SEQUENCE_ANCHORS)}")
    print(f"Closable surface anchors audited: {len(REQUIRED_CLOSABLE_SURFACE_ANCHORS)}")
    print(f"Graph closure surface anchors audited: {len(REQUIRED_GRAPH_CLOSURE_SURFACE_ANCHORS)}")
    print(f"Boundary anchors audited: {len(REQUIRED_BOUNDARY_ANCHORS)}")
    print(f"Root imports audited: {len(REQUIRED_ROOT_IMPORTS)}")
    print("Forbidden Lean tokens audited: sorry/admit/axiom/constant")

    if failures:
        print("Concrete analytic spine from scratch audit failed:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        raise SystemExit(1)

    print("Concrete analytic spine from scratch audit passed")


if __name__ == "__main__":
    main()
