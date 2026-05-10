#!/usr/bin/env python3
"""Audit Lean files for forbidden proof-gap tokens.

The script scans tracked source files by walking the repository tree. It is a
simple lexical guard for migration CI; it should be complemented by `lake build`.
"""

from __future__ import annotations

from pathlib import Path
import re
import sys

FORBIDDEN = ["sorry", "admit", "axiom", "constant"]
SKIP_DIRS = {".git", ".lake"}
TOKEN_RE = re.compile(r"\b(sorry|admit|axiom|constant)\b")


def iter_lean_files(root: Path):
    for path in root.rglob("*.lean"):
        if any(part in SKIP_DIRS for part in path.parts):
            continue
        yield path


def main() -> None:
    root = Path(".")
    counts = {token: 0 for token in FORBIDDEN}
    hits: list[tuple[str, int, str]] = []
    lean_files = 0

    for path in iter_lean_files(root):
        lean_files += 1
        text = path.read_text(encoding="utf-8")
        for lineno, line in enumerate(text.splitlines(), start=1):
            for match in TOKEN_RE.finditer(line):
                token = match.group(1)
                counts[token] += 1
                hits.append((str(path), lineno, token))

    print(f"Lean files scanned: {lean_files}")
    for token in FORBIDDEN:
        print(f"{token}: {counts[token]}")

    if hits:
        print("Forbidden token hits:", file=sys.stderr)
        for path, lineno, token in hits[:200]:
            print(f"  {path}:{lineno}: {token}", file=sys.stderr)
        if len(hits) > 200:
            print(f"  ... {len(hits) - 200} more hits omitted", file=sys.stderr)
        raise SystemExit(1)

    print("Lean forbidden-token audit passed")


if __name__ == "__main__":
    main()
