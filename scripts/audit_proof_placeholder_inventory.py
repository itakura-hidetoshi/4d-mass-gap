#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TOKENS = [
    "PUnit",
    "True",
    "StillOpen",
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


def main() -> int:
    files = []
    for base in [ROOT / "MGAP4D", ROOT / "docs"]:
        if not base.exists():
            print(f"missing scan directory: {base}")
            return 1
        files.extend(p for p in base.rglob("*") if p.suffix in {".lean", ".md"})

    hits = {token: [] for token in TOKENS}
    for path in sorted(files):
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
    for token in TOKENS:
        rows = hits[token]
        print(f"{token}: {len(rows)}")
        for rel, line_no, text in rows[:10]:
            print(f"  - {rel}:{line_no}: {text[:140]}")
        if len(rows) > 10:
            print(f"  ... {len(rows) - 10} more")
    print("Proof placeholder inventory audit completed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
