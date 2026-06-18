#!/usr/bin/env python3
"""Reject suspicious one-token replacements of changed Lean source files.

This guard is intentionally narrow. It catches destructive edits such as a
complete theorem file being replaced by the bare token ``invalid`` before the
expensive Lean parser/build lane starts. Empty or comment-only files are left to
Lean/project policy, and ordinary one-line commands such as ``import X`` remain
valid.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path
from typing import Iterable


BARE_IDENTIFIER_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")


def strip_lean_comments(text: str) -> str:
    """Remove nested block comments and line comments, preserving newlines."""

    out: list[str] = []
    i = 0
    depth = 0
    in_string = False
    escaped = False

    while i < len(text):
        if depth == 0 and in_string:
            ch = text[i]
            out.append(ch)
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_string = False
            i += 1
            continue

        if depth == 0 and text[i] == '"':
            in_string = True
            out.append(text[i])
            i += 1
            continue

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


def suspicious_bare_source(text: str) -> str | None:
    """Return the destructive bare token, if the whole source is one token."""

    cleaned = strip_lean_comments(text).strip()
    if BARE_IDENTIFIER_RE.fullmatch(cleaned):
        return cleaned
    return None


def audit_paths(paths: Iterable[Path]) -> list[str]:
    errors: list[str] = []
    for path in paths:
        if path.suffix != ".lean":
            continue
        if not path.exists():
            errors.append(f"{path}: changed Lean file does not exist")
            continue
        token = suspicious_bare_source(path.read_text(encoding="utf-8"))
        if token is not None:
            errors.append(
                f"{path}: suspicious one-token Lean source replacement: {token!r}"
            )
    return errors


def main(argv: list[str]) -> int:
    paths = [Path(arg) for arg in argv[1:] if arg.strip()]
    errors = audit_paths(paths)
    print(f"[source-integrity] Lean files audited: {len(paths)}")
    if errors:
        print("[source-integrity] FAILED")
        for error in errors:
            print(f"[source-integrity][error] {error}")
        return 1
    print("[source-integrity] passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
