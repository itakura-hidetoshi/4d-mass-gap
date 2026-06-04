#!/usr/bin/env python3
"""Fast static preflight audit for changed Lean files.

This script intentionally does not invoke Lean or Lake.  It is a cheap guard
that catches common edit / generation mistakes before the expensive kernel build
lane starts.  It is not a substitute for `lake build`.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path
from typing import Iterable

ROOT = Path.cwd()

DECL_RE = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable)\s+)?"
    r"(?:def|theorem|lemma|structure|inductive|abbrev|class|instance)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)\b"
)
IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_'.]+)\s*$")
LOCAL_IMPORT_RE = re.compile(r"^MGAP4D(?:\.|$)")

IMPOSSIBLE_ID_ID_ID_RE = re.compile(
    r"\|\s*SpectralMeasurePVMConcreteBoundedOperator\.identity\s*,\s*\n"
    r"\s*SpectralMeasurePVMConcreteBoundedOperator\.identity\s*=>\s*\n"
    r"\s*SpectralMeasurePVMConcreteBoundedOperator\.identity\b",
    re.MULTILINE,
)

TRY_RFL_FALSE_ELIM_RE = re.compile(
    r"try\s+rfl\s*\n\s*exact\s+False\.elim\b",
    re.MULTILINE,
)


def rel(path: Path) -> str:
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path)


def fail(errors: list[str], path: Path, line: int | None, message: str) -> None:
    loc = rel(path)
    if line is not None:
        loc += f":{line}"
    errors.append(f"{loc}: {message}")


def strip_line_comment(line: str) -> str:
    # Good enough for structural preflight; Lean strings are not interpreted here.
    return line.split("--", 1)[0]


def check_block_comments(path: Path, text: str, errors: list[str]) -> None:
    depth = 0
    line = 1
    i = 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if text.startswith("-/", i):
            if depth == 0:
                fail(errors, path, line, "unmatched block-comment close `-/`")
            else:
                depth -= 1
            i += 2
            continue
        if text[i] == "\n":
            line += 1
        i += 1
    if depth != 0:
        fail(errors, path, None, f"unterminated Lean block comment depth={depth}")


def check_imports(path: Path, lines: list[str], errors: list[str]) -> None:
    seen_non_import_command = False
    for idx, line in enumerate(lines, start=1):
        raw = strip_line_comment(line).strip()
        if not raw:
            continue
        if raw.startswith("/-") or raw.startswith("*/"):
            continue
        m = IMPORT_RE.match(raw)
        if m:
            if seen_non_import_command:
                fail(errors, path, idx, "Lean import appears after a non-import command")
            mod = m.group(1)
            if LOCAL_IMPORT_RE.match(mod):
                local_path = ROOT / (mod.replace(".", "/") + ".lean")
                if not local_path.exists():
                    fail(errors, path, idx, f"local import target is missing: {mod}")
            continue
        seen_non_import_command = True


def check_merge_conflicts(path: Path, lines: list[str], errors: list[str]) -> None:
    for idx, line in enumerate(lines, start=1):
        if line.startswith(("<<<<<<<", "=======", ">>>>>>>")):
            fail(errors, path, idx, "merge-conflict marker left in Lean file")


def check_r4_theorem_namespace(path: Path, lines: list[str], errors: list[str]) -> None:
    rel_path = rel(path)
    if not rel_path.startswith("MGAP4D/R4/Theorem/"):
        return
    required = ["namespace MGAP4D", "namespace R4", "namespace Theorem"]
    present = [line.strip() for line in lines if line.strip().startswith("namespace ")]
    for req in required:
        if req not in present:
            fail(errors, path, None, f"R4 theorem file missing `{req}`")
    tail = [line.strip() for line in lines if line.strip()]
    if len(tail) >= 3:
        expected_tail = ["end Theorem", "end R4", "end MGAP4D"]
        if tail[-3:] != expected_tail:
            fail(errors, path, None, f"R4 theorem file should end with {expected_tail}, got {tail[-3:]}")


def check_declaration_headers(path: Path, lines: list[str], errors: list[str]) -> None:
    for idx, line in enumerate(lines, start=1):
        raw = strip_line_comment(line)
        m = DECL_RE.match(raw)
        if not m:
            continue
        window = "\n".join(strip_line_comment(x) for x in lines[idx - 1 : min(len(lines), idx + 8)])
        if ":= by" in window or ":=" in window or " where" in window:
            continue
        fail(errors, path, idx, "declaration header has no nearby `:=` or `where` in the next 8 lines")


def check_known_hazard_patterns(path: Path, text: str, errors: list[str], warnings: list[str]) -> None:
    if IMPOSSIBLE_ID_ID_ID_RE.search(text):
        fail(
            errors,
            path,
            None,
            "concrete operator-add table maps identity+identity to identity; "
            "with disjoint `(whole, whole)` this can make `try rfl` consume the false branch",
        )
    if TRY_RFL_FALSE_ELIM_RE.search(text):
        warnings.append(
            f"{rel(path)}: proof uses `try rfl` followed by `exact False.elim`; "
            "preflight allows it, but the impossible branch must not be definitionally rfl"
        )


def collect_existing_declarations(changed: set[Path]) -> dict[str, list[Path]]:
    existing: dict[str, list[Path]] = {}
    for path in ROOT.glob("MGAP4D/**/*.lean"):
        if path in changed:
            continue
        try:
            lines = path.read_text(encoding="utf-8").splitlines()
        except UnicodeDecodeError:
            continue
        for line in lines:
            m = DECL_RE.match(strip_line_comment(line))
            if m:
                existing.setdefault(m.group(1), []).append(path)
    root_file = ROOT / "MGAP4D.lean"
    if root_file.exists() and root_file not in changed:
        for line in root_file.read_text(encoding="utf-8").splitlines():
            m = DECL_RE.match(strip_line_comment(line))
            if m:
                existing.setdefault(m.group(1), []).append(root_file)
    return existing


def check_declaration_reuse(
    path: Path,
    lines: list[str],
    existing: dict[str, list[Path]],
    seen_changed: dict[str, Path],
    errors: list[str],
) -> None:
    for idx, line in enumerate(lines, start=1):
        m = DECL_RE.match(strip_line_comment(line))
        if not m:
            continue
        name = m.group(1)
        if name in existing:
            locations = ", ".join(rel(p) for p in existing[name][:3])
            fail(errors, path, idx, f"declaration name already exists in repository: `{name}` at {locations}")
        if name in seen_changed and seen_changed[name] != path:
            fail(errors, path, idx, f"declaration name duplicated across changed files: `{name}` also in {rel(seen_changed[name])}")
        seen_changed[name] = path


def audit_file(
    path: Path,
    existing: dict[str, list[Path]],
    seen_changed: dict[str, Path],
    errors: list[str],
    warnings: list[str],
) -> None:
    if not path.exists():
        fail(errors, path, None, "changed Lean file does not exist")
        return
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()
    check_merge_conflicts(path, lines, errors)
    check_block_comments(path, text, errors)
    check_imports(path, lines, errors)
    check_r4_theorem_namespace(path, lines, errors)
    check_declaration_headers(path, lines, errors)
    check_known_hazard_patterns(path, text, errors, warnings)
    check_declaration_reuse(path, lines, existing, seen_changed, errors)


def normalize_args(args: Iterable[str]) -> list[Path]:
    paths: list[Path] = []
    for arg in args:
        if not arg.strip():
            continue
        p = (ROOT / arg).resolve()
        try:
            p.relative_to(ROOT)
        except ValueError:
            print(f"[preflight] ignoring non-repository path: {arg}", file=sys.stderr)
            continue
        if p.suffix == ".lean":
            paths.append(p)
    return sorted(set(paths))


def main(argv: list[str]) -> int:
    changed = normalize_args(argv[1:])
    if not changed:
        print("[preflight] no changed Lean files")
        return 0

    changed_set = set(changed)
    existing = collect_existing_declarations(changed_set)
    errors: list[str] = []
    warnings: list[str] = []
    seen_changed: dict[str, Path] = {}

    for path in changed:
        audit_file(path, existing, seen_changed, errors, warnings)

    print(f"[preflight] changed Lean files audited: {len(changed)}")
    for warning in warnings:
        print(f"[preflight][warn] {warning}")

    if errors:
        print("[preflight] FAILED")
        for err in errors:
            print(f"[preflight][error] {err}")
        return 1

    print("[preflight] passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
