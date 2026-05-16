#!/usr/bin/env python3
"""Audit the infinite-dimensional Yang--Mills target-obligation layer.

This guard checks that the repository's evolution beyond skeleton-only closure
is represented as an explicit Lean target surface with named analytic
obligations and public-boundary markers.

It is a syntactic/contract audit. Lean kernel checking remains `lake build`.
"""

from __future__ import annotations

from pathlib import Path
import re
import sys

STRING_RE = re.compile(r'"(?:[^"\\]|\\.)*"')
FORBIDDEN_TOKENS_RE = re.compile(r"\b(sorry|admit|axiom|constant)\b")
TARGET_PATH = Path("MGAP4D/MathlibAnalytic/InfiniteDimensionalYangMillsRealizationTargets.lean")
ROOT_PATH = Path("MGAP4D/MathlibAnalytic.lean")
DOC_PATH = Path("docs/infinite_dimensional_yang_mills_target_layer.md")

REQUIRED_TARGET_ANCHORS = (
    "InfiniteDimensionalYangMillsRealizationTarget",
    "InfiniteDimensionalYangMillsRealizationTarget.ready",
    "InfiniteDimensionalYangMillsTargetReviewSurface",
    "infinite_dimensional_yang_mills_target_review_surface_ready",
    "infinite_dimensional_witness",
    "separable_hilbert_witness",
    "dense_core_witness",
    "domain_density_witness",
    "hphys_symmetric_witness",
    "hphys_self_adjoint_witness",
    "gauge_invariance_witness",
    "yang_mills_energy_witness",
    "continuum_limit_witness",
    "os_positivity_witness",
    "spectral_theorem_witness",
    "exact_atom_witness",
    "plaquette_nonzero_weight_witness",
    "vacuum_orthogonal_nonempty_witness",
    "normalized_gap_eq_exact",
    "exact_value_eq_3320",
    "publicBoundaryHeld",
    "finalReleaseHeld",
)

REQUIRED_THEOREM_ANCHORS = (
    "infinite_dimensional_target_requires_infinite_dimension",
    "infinite_dimensional_target_requires_self_adjoint_hphys",
    "infinite_dimensional_target_requires_continuum_limit",
    "infinite_dimensional_target_requires_plaquette_weight",
    "infinite_dimensional_target_normalized_gap_eq_exact",
    "infinite_dimensional_target_exact_value_eq_3320",
    "infinite_dimensional_target_public_boundary_held",
    "infinite_dimensional_target_final_release_held",
)

REQUIRED_ROOT_ANCHORS = (
    "import MGAP4D.MathlibAnalytic.InfiniteDimensionalYangMillsRealizationTargets",
)

REQUIRED_DOC_ANCHORS = (
    "Infinite-dimensional Yang--Mills Target Layer",
    "proof-obligation",
    "infinite-dimensional Hilbert realization",
    "self-adjoint H_phys",
    "continuum limit",
    "positive plaquette spectral weight",
    "nonempty vacuum-orthogonal sector",
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
        return [f"missing target file for forbidden-token audit: {path}"]
    source = cleaned_lean_source(path)
    hits: list[str] = []
    for lineno, line in enumerate(source.splitlines(), start=1):
        if FORBIDDEN_TOKENS_RE.search(line):
            hits.append(f"{path}:{lineno}: forbidden token in target-layer audit")
    return hits


def main() -> None:
    failures: list[str] = []
    failures.extend(audit_forbidden_tokens(TARGET_PATH))
    failures.extend(require(TARGET_PATH, REQUIRED_TARGET_ANCHORS, "target-layer", clean_lean=True))
    failures.extend(require(TARGET_PATH, REQUIRED_THEOREM_ANCHORS, "target theorem", clean_lean=True))
    failures.extend(require(ROOT_PATH, REQUIRED_ROOT_ANCHORS, "root import", clean_lean=True))
    failures.extend(require(DOC_PATH, REQUIRED_DOC_ANCHORS, "target-layer documentation", clean_lean=False))

    print("Infinite-dimensional Yang-Mills target layer audit")
    print(f"Target anchors audited: {len(REQUIRED_TARGET_ANCHORS)}")
    print(f"Target theorem anchors audited: {len(REQUIRED_THEOREM_ANCHORS)}")
    print("Root import audited: MGAP4D/MathlibAnalytic.lean")
    print("Documentation audited: docs/infinite_dimensional_yang_mills_target_layer.md")
    print("Forbidden Lean tokens audited: sorry/admit/axiom/constant")

    if failures:
        print("Infinite-dimensional target layer audit failed:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        raise SystemExit(1)

    print("Infinite-dimensional target layer audit passed")


if __name__ == "__main__":
    main()
