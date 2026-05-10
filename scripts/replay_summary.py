#!/usr/bin/env python3
"""Summarize the current Lean source tree for local replay checks.

This script is intentionally lightweight: it does not prove the project by
itself. It records source-tree size, import count, and declaration-like lines so
that CI and local runs can track migration growth over time.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import json
import re

SKIP_DIRS = {".git", ".lake"}
DECL_RE = re.compile(r"^\s*(def|theorem|lemma|structure|inductive|class|instance|abbrev)\b")
IMPORT_RE = re.compile(r"^\s*import\s+")
NAMESPACE_RE = re.compile(r"^\s*namespace\s+")


@dataclass
class ReplaySummary:
    lean_files: int = 0
    imports: int = 0
    declaration_like_lines: int = 0
    namespace_lines: int = 0
    total_lines: int = 0

    def to_dict(self) -> dict[str, int]:
        return {
            "lean_files": self.lean_files,
            "imports": self.imports,
            "declaration_like_lines": self.declaration_like_lines,
            "namespace_lines": self.namespace_lines,
            "total_lines": self.total_lines,
        }


def iter_lean_files(root: Path):
    for path in sorted(root.rglob("*.lean")):
        if any(part in SKIP_DIRS for part in path.parts):
            continue
        yield path


def summarize(root: Path) -> ReplaySummary:
    summary = ReplaySummary()
    for path in iter_lean_files(root):
        summary.lean_files += 1
        text = path.read_text(encoding="utf-8")
        for line in text.splitlines():
            summary.total_lines += 1
            if IMPORT_RE.match(line):
                summary.imports += 1
            if DECL_RE.match(line):
                summary.declaration_like_lines += 1
            if NAMESPACE_RE.match(line):
                summary.namespace_lines += 1
    return summary


def main() -> None:
    summary = summarize(Path("."))
    print("Lean replay summary")
    for key, value in summary.to_dict().items():
        print(f"{key}: {value}")

    out = Path("maps/REPLAY_SUMMARY_CURRENT.json")
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(summary.to_dict(), indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
