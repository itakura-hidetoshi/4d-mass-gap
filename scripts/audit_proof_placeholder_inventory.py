#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

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

TOKENS = OPEN_DEBT_TOKENS + PROVENANCE_TOKENS


def collect_files():
    files = []
    for base in [ROOT / "MGAP4D", ROOT / "docs"]:
        if not base.exists():
            print(f"missing scan directory: {base}")
            return []
        files.extend(p for p in base.rglob("*") if p.suffix in {".lean", ".md"})
    return sorted(files)


def main() -> int:
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

    print("Proof placeholder inventory audit completed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
