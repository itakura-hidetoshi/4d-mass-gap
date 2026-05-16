#!/usr/bin/env python3
"""Audit the internal review residual closure gate."""

from __future__ import annotations

from pathlib import Path
import re
import sys

STRING_RE = re.compile(r'"(?:[^"\\]|\\.)*"')
FORBIDDEN_TOKENS_RE = re.compile(r"\b(sorry|admit|axiom|constant)\b")
TARGET_PATH = Path("MGAP4D/MathlibAnalytic/InternalReviewResidualClosureGate.lean")
ROOT_PATH = Path("MGAP4D/MathlibAnalytic.lean")
DOC_PATH = Path("docs/internal_review_residual_closure_gate.md")

REQUIRED_TARGET_ANCHORS = (
    "InternalReviewResidualClosureGateData",
    "InternalReviewResidualClosureGateData.ready",
    "internalReviewResidualClosureGateData",
    "internal_review_residual_closure_gate_ready",
    "fourLaneClosureReady",
    "exactValueOriginReady",
    "finalReleaseClosureReady",
    "repositoryInternalResidualClosed",
    "noReviewLevelResidualLeft",
    "exactTheoremBodyOriginPreserved",
    "notPackagingArtifactPreserved",
    "notCILedgerArtifactPreserved",
    "finalReleaseClosureLinked",
    "externalReviewBoundaryVisible",
    "publicBoundaryHeld",
    "finalReleaseHeld",
    "exactValuePreserved",
)

REQUIRED_THEOREM_ANCHORS = (
    "internal_review_residual_gate_repository_residual_closed",
    "internal_review_residual_gate_no_review_level_residual_left",
    "internal_review_residual_gate_exact_origin_preserved",
    "internal_review_residual_gate_not_packaging_artifact_preserved",
    "internal_review_residual_gate_not_ci_ledger_artifact_preserved",
    "internal_review_residual_gate_final_release_closure_linked",
    "internal_review_residual_gate_external_review_boundary_visible",
    "internal_review_residual_gate_public_boundary_held",
    "internal_review_residual_gate_final_release_held",
    "internal_review_residual_gate_exact_value_preserved",
)

REQUIRED_ROOT_ANCHORS = (
    "import MGAP4D.MathlibAnalytic.InternalReviewResidualClosureGate",
)

REQUIRED_DOC_ANCHORS = (
    "Internal Review Residual Closure Gate",
    "repositoryInternalResidualClosed",
    "noReviewLevelResidualLeft",
    "exactTheoremBodyOriginPreserved",
    "finalReleaseClosureLinked",
    "externalReviewBoundaryVisible",
    "publicBoundaryHeld",
    "finalReleaseHeld",
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
        return [f"missing internal review closure gate file for forbidden-token audit: {path}"]
    source = cleaned_lean_source(path)
    hits: list[str] = []
    for lineno, line in enumerate(source.splitlines(), start=1):
        if FORBIDDEN_TOKENS_RE.search(line):
            hits.append(f"{path}:{lineno}: forbidden token in internal review closure gate audit")
    return hits


def main() -> None:
    failures: list[str] = []
    failures.extend(audit_forbidden_tokens(TARGET_PATH))
    failures.extend(require(TARGET_PATH, REQUIRED_TARGET_ANCHORS, "internal review closure gate target", clean_lean=True))
    failures.extend(require(TARGET_PATH, REQUIRED_THEOREM_ANCHORS, "internal review closure gate theorem", clean_lean=True))
    failures.extend(require(ROOT_PATH, REQUIRED_ROOT_ANCHORS, "root import", clean_lean=True))
    failures.extend(require(DOC_PATH, REQUIRED_DOC_ANCHORS, "internal review closure gate documentation", clean_lean=False))

    print("Internal review residual closure gate audit")
    print(f"Internal closure gate anchors audited: {len(REQUIRED_TARGET_ANCHORS)}")
    print(f"Internal closure gate theorem anchors audited: {len(REQUIRED_THEOREM_ANCHORS)}")
    print("Root import audited: MGAP4D/MathlibAnalytic.lean")
    print("Documentation audited: docs/internal_review_residual_closure_gate.md")
    print("Forbidden Lean tokens audited: sorry/admit/axiom/constant")

    if failures:
        print("Internal review residual closure gate audit failed:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        raise SystemExit(1)

    print("Internal review residual closure gate audit passed")


if __name__ == "__main__":
    main()
