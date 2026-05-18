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
    "concreteAnalyticSpineR1Ready",
    "concreteAnalyticSpineR2DomainSurfaceReady",
    "concrete_analytic_spine_r1_ready",
    "concrete_analytic_spine_r2_domain_surface_ready",
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

REQUIRED_BOUNDARY_ANCHORS = (
    "not yet the physical Hamiltonian domain",
    "not yet a claim of a physical",
    "does not assert unboundedness",
    "self-adjointness",
    "PVM",
    "physical 4D Yang--Mills Hamiltonian",
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
    failures.extend(require(TARGET_PATH, REQUIRED_BOUNDARY_ANCHORS, "boundary", clean_lean=False))
    failures.extend(require(ROOT_PATH, REQUIRED_ROOT_IMPORTS, "root import", clean_lean=False))
    failures.extend(forbid(TARGET_PATH, FORBIDDEN_PREMATURE_CLAIMS, "premature closure", clean_lean=False))

    print("Concrete analytic spine from scratch audit")
    print(f"Target anchors audited: {len(REQUIRED_TARGET_ANCHORS)}")
    print(f"Mathlib typeclass anchors audited: {len(REQUIRED_MATHLIB_TYPECLASS_ANCHORS)}")
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
