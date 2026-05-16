#!/usr/bin/env python3
"""Audit the external audit readiness gate field-classification documentation."""

from __future__ import annotations

from pathlib import Path
import re
import sys

DOC_PATH = Path("docs/external_audit_readiness_gate_field_classification.md")
TARGET_PATH = Path("MGAP4D/MathlibAnalytic/ExternalAuditReadinessGate.lean")

REQUIRED_FIELDS = (
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

REQUIRED_WITNESS_CLASSES = (
    "theorem-derived",
    "script-route",
    "documentation-route",
    "boundary-governance",
)

REQUIRED_BOUNDARY_PHRASES = (
    "external audit completed",
    "external mathematical consensus obtained",
    "final theorem release opened",
    "External consensus claimed: no",
    "Final theorem release opened: no",
    "Lean semantics changed: no",
)


def read(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"missing required file: {path}")
    return path.read_text(encoding="utf-8")


def field_names_from_structure(source: str) -> set[str]:
    match = re.search(
        r"structure\s+ExternalAuditReadinessGateData\s+where\n(?P<body>.*?)(?:\n\ndef|\n\ntheorem|\nnamespace|\nend)",
        source,
        flags=re.S,
    )
    if not match:
        raise ValueError("could not locate ExternalAuditReadinessGateData structure body")
    fields: set[str] = set()
    for line in match.group("body").splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith("--"):
            continue
        if ":" not in stripped:
            continue
        name = stripped.split(":", 1)[0].strip()
        if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", name):
            fields.add(name)
    return fields


def require_all(text: str, anchors: tuple[str, ...], label: str) -> list[str]:
    return [f"missing {label} anchor {anchor!r} in {DOC_PATH}" for anchor in anchors if anchor not in text]


def main() -> None:
    failures: list[str] = []

    try:
        doc = read(DOC_PATH)
    except FileNotFoundError as exc:
        failures.append(str(exc))
        doc = ""

    try:
        target = read(TARGET_PATH)
        actual_fields = field_names_from_structure(target)
    except (FileNotFoundError, ValueError) as exc:
        failures.append(str(exc))
        actual_fields = set()

    expected_fields = set(REQUIRED_FIELDS)
    missing_from_expected = actual_fields - expected_fields
    stale_expected = expected_fields - actual_fields if actual_fields else set()
    if missing_from_expected:
        failures.append(
            "ExternalAuditReadinessGateData has fields missing from REQUIRED_FIELDS: "
            + ", ".join(sorted(missing_from_expected))
        )
    if stale_expected:
        failures.append(
            "REQUIRED_FIELDS contains names not found in ExternalAuditReadinessGateData: "
            + ", ".join(sorted(stale_expected))
        )

    failures.extend(require_all(doc, REQUIRED_FIELDS, "field-classification field"))
    failures.extend(require_all(doc, REQUIRED_WITNESS_CLASSES, "field-classification witness class"))
    failures.extend(require_all(doc, REQUIRED_BOUNDARY_PHRASES, "field-classification boundary phrase"))

    table_rows = [line for line in doc.splitlines() if line.startswith("| `")]
    documented_row_fields = {
        row.split("|", 2)[1].strip().strip("`")
        for row in table_rows
        if "|" in row
    }
    missing_table_rows = expected_fields - documented_row_fields
    if missing_table_rows:
        failures.append(
            "field-classification table is missing rows for: "
            + ", ".join(sorted(missing_table_rows))
        )

    print("External audit readiness gate field-classification audit")
    print(f"Fields audited: {len(REQUIRED_FIELDS)}")
    print(f"Witness classes audited: {len(REQUIRED_WITNESS_CLASSES)}")
    print("Boundary phrases audited: external audit / consensus / release boundaries")
    print(f"Documentation audited: {DOC_PATH}")

    if failures:
        print("External audit readiness gate field-classification audit failed:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        raise SystemExit(1)

    print("External audit readiness gate field-classification audit passed")


if __name__ == "__main__":
    main()
