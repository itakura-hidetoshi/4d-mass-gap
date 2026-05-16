#!/usr/bin/env python3
"""Audit the external audit readiness replay certificate documentation."""

from __future__ import annotations

from pathlib import Path
import sys

DOC_PATH = Path("docs/external_audit_readiness_replay_certificate.md")
CHECK_PATH = Path("scripts/check.sh")
GATE_PATH = Path("MGAP4D/MathlibAnalytic/ExternalAuditReadinessGate.lean")

REQUIRED_CERTIFICATE_ANCHORS = (
    "Checkpoint commit: de76fd42f0e5c3bfd58090bfb2eef2510f6b5d63",
    "Workflow run: 25973699153",
    "Workflow job: 76350067649",
    "bash scripts/check.sh",
    "Build completed successfully (8368 jobs).",
    "Lean files scanned: 457",
    "sorry: 0",
    "admit: 0",
    "axiom: 0",
    "constant: 0",
    "Major theorem specs audited: 12",
    "Bridge files audited: 8",
    "lean_files: 457",
    "imports: 1191",
    "declaration_like_lines: 2663",
    "total_lines: 27611",
    "MGAP4D.MathlibAnalytic.ExternalAuditReadinessGate",
    "exactGapValueReal = (33 : ℝ) / 20",
    "external_audit_readiness_gate_ready",
)

REQUIRED_GATE_THEOREMS = (
    "external_audit_readiness_internal_gate_ready_witness",
    "external_audit_readiness_bundle_manifest_ready_witness",
    "external_audit_readiness_chain_index_ready_witness",
    "external_audit_readiness_repository_internal_residual_closed_witness",
    "external_audit_readiness_no_review_level_residual_left_witness",
    "external_audit_readiness_independent_replay_visible_witness",
    "external_audit_readiness_audit_script_route_visible_witness",
    "external_audit_readiness_ci_route_visible_witness",
    "external_audit_readiness_external_audit_ready_witness",
    "external_audit_readiness_external_consensus_not_claimed_witness",
    "external_audit_readiness_public_boundary_held_witness",
    "external_audit_readiness_final_release_held_witness",
    "external_audit_readiness_exact_value_preserved_witness",
    "external_audit_readiness_gate_ready",
)

REQUIRED_BOUNDARY_PHRASES = (
    "external audit completed",
    "external mathematical consensus obtained",
    "final theorem release opened",
    "future residuals impossible",
    "public theorem boundary removed",
    "Lean semantics changed: no",
    "External consensus claimed: no",
    "External audit completed: no",
    "Final theorem release opened: no",
)

REQUIRED_CHECK_ROUTE_ANCHORS = (
    "python3 scripts/audit_external_audit_readiness_gate.py",
    "python3 scripts/audit_external_audit_readiness_gate_field_classification.py",
    "lake build MGAP4D.MathlibAnalytic.ExternalAuditReadinessGate",
    "lake build",
)


def read(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"missing required file: {path}")
    return path.read_text(encoding="utf-8")


def require_all(text: str, anchors: tuple[str, ...], label: str, path: Path) -> list[str]:
    return [f"missing {label} anchor {anchor!r} in {path}" for anchor in anchors if anchor not in text]


def main() -> None:
    failures: list[str] = []

    try:
        doc = read(DOC_PATH)
    except FileNotFoundError as exc:
        failures.append(str(exc))
        doc = ""

    try:
        check = read(CHECK_PATH)
    except FileNotFoundError as exc:
        failures.append(str(exc))
        check = ""

    try:
        gate = read(GATE_PATH)
    except FileNotFoundError as exc:
        failures.append(str(exc))
        gate = ""

    failures.extend(require_all(doc, REQUIRED_CERTIFICATE_ANCHORS, "replay-certificate", DOC_PATH))
    failures.extend(require_all(doc, REQUIRED_GATE_THEOREMS, "gate-theorem", DOC_PATH))
    failures.extend(require_all(doc, REQUIRED_BOUNDARY_PHRASES, "boundary", DOC_PATH))
    failures.extend(require_all(check, REQUIRED_CHECK_ROUTE_ANCHORS, "check-route", CHECK_PATH))
    failures.extend(require_all(gate, REQUIRED_GATE_THEOREMS, "gate-theorem", GATE_PATH))

    print("External audit readiness replay certificate audit")
    print(f"Certificate anchors audited: {len(REQUIRED_CERTIFICATE_ANCHORS)}")
    print(f"Gate theorem anchors audited: {len(REQUIRED_GATE_THEOREMS)}")
    print("Boundary phrases audited: external audit / consensus / release boundaries")
    print(f"Documentation audited: {DOC_PATH}")

    if failures:
        print("External audit readiness replay certificate audit failed:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        raise SystemExit(1)

    print("External audit readiness replay certificate audit passed")


if __name__ == "__main__":
    main()