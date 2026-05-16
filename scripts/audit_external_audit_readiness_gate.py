#!/usr/bin/env python3
"""Audit the external audit readiness gate."""

from __future__ import annotations

from pathlib import Path
import re
import sys

STRING_RE = re.compile(r'"(?:[^"\\]|\\.)*"')
FORBIDDEN_TOKENS_RE = re.compile(r"\b(sorry|admit|axiom|constant)\b")
TARGET_PATH = Path("MGAP4D/MathlibAnalytic/ExternalAuditReadinessGate.lean")
DOC_PATH = Path("docs/external_audit_readiness_gate.md")

REQUIRED_TARGET_ANCHORS = (
    "ExternalAuditReadinessGateData",
    "ExternalAuditReadinessGateData.ready",
    "externalAuditReadinessGateData",
    "external_audit_readiness_gate_ready",
    "internalGateReady",
    "bundleManifestReady",
    "chainIndexReady",
    "repositoryInternalResidualClosed",
    "noReviewLevelResidualLeft",
    "independentReplayVisible",
    "auditScriptRouteVisible",
    "ciRouteVisible",
    "externalAuditReady",
    "externalConsensusNotClaimed",
    "publicBoundaryHeld",
    "finalReleaseHeld",
    "exactValuePreserved",
)

REQUIRED_THEOREM_ANCHORS = (
    "external_audit_readiness_repository_internal_residual_closed",
    "external_audit_readiness_no_review_level_residual_left",
    "external_audit_readiness_independent_replay_visible",
    "external_audit_readiness_audit_script_route_visible",
    "external_audit_readiness_ci_route_visible",
    "external_audit_readiness_external_audit_ready",
    "external_audit_readiness_external_consensus_not_claimed",
    "external_audit_readiness_public_boundary_held",
    "external_audit_readiness_final_release_held",
    "external_audit_readiness_exact_value_preserved",
)

REQUIRED_DOC_ANCHORS = (
    "External Audit Readiness Gate",
    "repositoryInternalResidualClosed",
    "noReviewLevelResidualLeft",
    "independentReplayVisible",
    "auditScriptRouteVisible",
    "ciRouteVisible",
    "externalAuditReady",
    "externalConsensusNotClaimed",
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
        return [f"missing external audit readiness gate file for forbidden-token audit: {path}"]
    source = cleaned_lean_source(path)
    hits: list[str] = []
    for lineno, line in enumerate(source.splitlines(), start=1):
        if FORBIDDEN_TOKENS_RE.search(line):
            hits.append(f"{path}:{lineno}: forbidden token in external audit readiness gate audit")
    return hits


def main() -> None:
    failures: list[str] = []
    failures.extend(audit_forbidden_tokens(TARGET_PATH))
    failures.extend(require(TARGET_PATH, REQUIRED_TARGET_ANCHORS, "external audit readiness target", clean_lean=True))
    failures.extend(require(TARGET_PATH, REQUIRED_THEOREM_ANCHORS, "external audit readiness theorem", clean_lean=True))
    failures.extend(require(DOC_PATH, REQUIRED_DOC_ANCHORS, "external audit readiness documentation", clean_lean=False))

    print("External audit readiness gate audit")
    print(f"External audit readiness anchors audited: {len(REQUIRED_TARGET_ANCHORS)}")
    print(f"External audit readiness theorem anchors audited: {len(REQUIRED_THEOREM_ANCHORS)}")
    print("Documentation audited: docs/external_audit_readiness_gate.md")
    print("Forbidden Lean tokens audited: sorry/admit/axiom/constant")

    if failures:
        print("External audit readiness gate audit failed:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        raise SystemExit(1)

    print("External audit readiness gate audit passed")


if __name__ == "__main__":
    main()
