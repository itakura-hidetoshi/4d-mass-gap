#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
INVENTORY_DOC = ROOT / "docs/proof_placeholder_inventory.md"

OPEN_DEBT_TOKENS = [
    "PUnit",
    "True",
    "StillOpen",
]

PROVENANCE_TOKENS = [
    "theoremWitnessOnly",
    "receipt",
    "Receipt",
    "ready",
    "Ready",
    "prototype",
    "Prototype",
    "skeleton",
    "Skeleton",
    "boundary",
    "Boundary",
    "packet",
    "Packet",
    "manifest",
    "Manifest",
]

REQUIRED_INVENTORY_ANCHORS = [
    "Euclidean construction target / spine interpretation",
    "EuclideanYangMillsMeasureUnconditionalConstructionTarget",
    "EuclideanYangMillsContinuumMeasureConstructionSpine",
    "ExternalAuditReadinessEuclideanYangMillsConstructionSpineProjection",
    "continuumFourDimensionalYangMillsMeasureConstructed_proof",
    "nontrivialCompactGaugeGroupConstructed_proof",
    "interactingContinuumLimitConstructed_proof",
    "gaugeInvariantSchwingerFunctionsConstructed_proof",
    "projectiveConsistency_proof",
    "tightness_proof",
    "weakLimitExists_proof",
    "continuumMeasureIdentified_proof",
    "schwingerFunctionsAreContinuumLimits_proof",
    "euclidean_yang_mills_unconditional_measure_construction_mass_gap",
    "euclidean_yang_mills_finite_volume_continuum_construction_mass_gap",
    "external_audit_readiness_euclidean_yang_mills_construction_spine_projection",
    "external_audit_readiness_euclidean_construction_spine_exact_gap_positive",
    "external_audit_readiness_euclidean_construction_spine_exact_gap_threshold",
    "external_audit_readiness_euclidean_construction_spine_pvm_detects_first_excitation",
    "The construction-spine external-audit projection is not external acceptance.",
    "External acceptance of the construction-spine external-audit projection is not claimed.",
]

TOKENS = OPEN_DEBT_TOKENS + PROVENANCE_TOKENS


def collect_files():
    files = []
    for base in [ROOT / "MGAP4D", ROOT / "docs"]:
        if not base.exists():
            print(f"missing scan directory: {base}")
            return []
        files.extend(p for p in base.rglob("*") if p.suffix in {".lean", ".md"})
    return sorted(files)


def audit_required_inventory_anchors() -> list[str]:
    if not INVENTORY_DOC.exists():
        return [f"missing inventory doc: {INVENTORY_DOC.relative_to(ROOT)}"]
    text = INVENTORY_DOC.read_text(encoding="utf-8")
    failures = []
    for anchor in REQUIRED_INVENTORY_ANCHORS:
        if anchor not in text:
            failures.append(
                f"docs/proof_placeholder_inventory.md missing construction proof-debt anchor: {anchor!r}"
            )
    return failures


def main() -> int:
    failures = audit_required_inventory_anchors()
    files = collect_files()
    if not files:
        return 1

    hits = {token: [] for token in TOKENS}
    for path in files:
        rel = path.relative_to(ROOT).as_posix()
        try:
            lines = path.read_text(encoding="utf-8").splitlines()
        except UnicodeDecodeError:
            continue
        for i, line in enumerate(lines, 1):
            for token in TOKENS:
                if token in line:
                    hits[token].append((rel, i, line.strip()))

    print("Proof placeholder inventory audit")
    print(f"files scanned: {len(files)}")
    print("Open proof-debt markers: PUnit / True / StillOpen")
    print("These markers do not close analytic theorem obligations unless replaced, discharged, or explicitly superseded by typed theorem anchors.")

    for token in OPEN_DEBT_TOKENS:
        rows = hits[token]
        print(f"OPEN_PROOF_DEBT {token}: {len(rows)}")
        for rel, line_no, text in rows[:10]:
            print(f"  - {rel}:{line_no}: {text[:140]}")
        if len(rows) > 10:
            print(f"  ... {len(rows) - 10} more")

    print("Provenance / readiness / review-order markers")
    for token in PROVENANCE_TOKENS:
        rows = hits[token]
        print(f"PROVENANCE_OR_READY {token}: {len(rows)}")
        for rel, line_no, text in rows[:8]:
            print(f"  - {rel}:{line_no}: {text[:140]}")
        if len(rows) > 8:
            print(f"  ... {len(rows) - 8} more")

    if failures:
        print("Proof placeholder inventory audit failed:")
        for failure in failures:
            print(f"  {failure}")
        return 1

    print(f"Euclidean construction proof-debt anchors audited: {len(REQUIRED_INVENTORY_ANCHORS)}")
    print("Proof placeholder inventory audit completed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
