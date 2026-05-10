#!/usr/bin/env python3
"""Audit Lean files for forbidden proof-gap declarations.

This is a migration CI guard. It scans Lean source after removing comments and
string literals, then rejects proof-gap declarations/tactics that should not
enter the finalized MGAP4D source tree.
"""

from __future__ import annotations

from pathlib import Path
import re
import sys

FORBIDDEN = ["sorry", "admit", "axiom", "constant"]
SKIP_DIRS = {".git", ".lake"}
TOKEN_RE = re.compile(r"\b(sorry|admit|axiom|constant)\b")
STRING_RE = re.compile(r'"(?:[^"\\]|\\.)*"')


def strip_lean_comments(text: str) -> str:
    """Remove Lean line comments and nested block comments conservatively."""
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


def strip_strings(text: str) -> str:
    return STRING_RE.sub('""', text)


def cleaned_source(text: str) -> str:
    return strip_strings(strip_lean_comments(text))


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
        text = cleaned_source(path.read_text(encoding="utf-8"))
        for lineno, line in enumerate(text.splitlines(), start=1):
            for match in TOKEN_RE.finditer(line):
                token = match.group(1)
                counts[token] += 1
                hits.append((str(path), lineno, token))

    print(f"Lean files scanned: {lean_files}")
    for token in FORBIDDEN:
        print(f"{token}: {counts[token]}")

    if hits:
        print("Forbidden Lean token hits:", file=sys.stderr)
        for path, lineno, token in hits[:200]:
            print(f"  {path}:{lineno}: {token}", file=sys.stderr)
        if len(hits) > 200:
            print(f"  ... {len(hits) - 200} more hits omitted", file=sys.stderr)
        raise SystemExit(1)

    print("Lean forbidden-token audit passed")


if __name__ == "__main__":
    main()
