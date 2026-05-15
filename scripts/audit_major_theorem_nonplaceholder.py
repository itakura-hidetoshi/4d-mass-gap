#!/usr/bin/env python3
"""Audit major theorem surfaces for non-placeholder statements.

This guard complements `audit_lean_forbidden_tokens.py`.

It does not attempt to replace Lean's kernel.  Instead, it checks that the
named load-bearing theorem surfaces are present and that their theorem
statements are not merely `True`/placeholder statements.  Each audited theorem
must contain domain-specific anchors such as the exact value `33/20`, positivity,
spectral weight, PVM mass compatibility, or normalization equations.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import re
import sys

SKIP_DIRS = {".git", ".lake"}
STRING_RE = re.compile(r'"(?:[^"\\]|\\.)*"')
FORBIDDEN_TOKENS_RE = re.compile(r"\b(sorry|admit|axiom|constant)\b")
TRIVIAL_TRUE_THEOREM_RE = re.compile(
    r"\btheorem\s+([A-Za-z0-9_'.]+)[\s\S]*?:\s*(?:\(?\s*)?True\s*(?:\)?\s*)?:=",
    re.MULTILINE,
)
THEOREM_RE_TEMPLATE = r"\btheorem\s+{name}\b([\s\S]*?):="


@dataclass(frozen=True)
class TheoremAuditSpec:
    path: str
    name: str
    required_any: tuple[str, ...]
    required_all: tuple[str, ...] = ()


MAJOR_THEOREMS: tuple[TheoremAuditSpec, ...] = (
    TheoremAuditSpec(
        path="MGAP4D/MathlibAnalytic/ExactGapTheoremBodyClosure.lean",
        name="exact_gap_theorem_body_closure_value",
        required_any=("exactGapValueReal_eq", "(33 : ℝ) / 20", "exactValue_eq_3320"),
        required_all=("exactGapTheoremBodyClosure",),
    ),
    TheoremAuditSpec(
        path="MGAP4D/MathlibAnalytic/ExactGapTheoremBodyClosure.lean",
        name="exact_gap_theorem_body_closure_positive",
        required_any=("exactGapValueReal_pos", "0 < exactGapValueReal"),
        required_all=("exactGapTheoremBodyClosure",),
    ),
    TheoremAuditSpec(
        path="MGAP4D/MathlibAnalytic/ExactGapTheoremBodyClosure.lean",
        name="exact_gap_theorem_body_closure_weight_positive",
        required_any=("observableWeightPositive", "spectralWeight", "positive_weight"),
    ),
    TheoremAuditSpec(
        path="MGAP4D/MathlibAnalytic/ExactGapTheoremBodyClosure.lean",
        name="exact_gap_theorem_body_closure_weight_equals_pvm_mass",
        required_any=("observableWeightEqualsPVMMass", "projectionMass", "pvm_mass"),
    ),
    TheoremAuditSpec(
        path="MGAP4D/MathlibAnalytic/OperatorMeasureCompatibilityTheorem.lean",
        name="operator_measure_compatibility_weight_equals_pvm_mass",
        required_any=("projectionMass", "spectralWeight"),
        required_all=("constructedObservable", "exactAtom"),
    ),
    TheoremAuditSpec(
        path="MGAP4D/MathlibAnalytic/OperatorMeasureCompatibilityTheorem.lean",
        name="operator_measure_compatibility_positive_weight",
        required_any=("0 <", "spectralWeight"),
        required_all=("constructedObservable", "exactAtom"),
    ),
    TheoremAuditSpec(
        path="MGAP4D/MathlibAnalytic/PhysicalHamiltonianNormalizationBridge.lean",
        name="physical_hamiltonian_normalized_gap_def",
        required_any=("normalizedGap",),
        required_all=("physicalGap", "referenceEnergyScale"),
    ),
    TheoremAuditSpec(
        path="MGAP4D/MathlibAnalytic/PhysicalHamiltonianNormalizationBridge.lean",
        name="physical_hamiltonian_gap_reconstruction",
        required_any=("physicalGap",),
        required_all=("referenceEnergyScale", "normalizedGap"),
    ),
    TheoremAuditSpec(
        path="MGAP4D/MathlibAnalytic/PhysicalHamiltonianNormalizationBridge.lean",
        name="physical_hamiltonian_normalized_gap_eq_3320",
        required_any=("(33 : ℝ) / 20", "exactGapValueReal"),
        required_all=("normalizedGap",),
    ),
    TheoremAuditSpec(
        path="MGAP4D/MathlibAnalytic/ExactValueTheoremBodyOrigin.lean",
        name="exact_value_origin_from_theorem_body",
        required_any=("(33 : ℝ) / 20", "exactValueFromTheoremBody"),
        required_all=("exactGapValueReal",),
    ),
    TheoremAuditSpec(
        path="MGAP4D/MathlibAnalytic/ExactValueTheoremBodyOrigin.lean",
        name="exact_value_origin_not_packaging_artifact",
        required_any=("notPackagingArtifact",),
    ),
    TheoremAuditSpec(
        path="MGAP4D/MathlibAnalytic/ExactValueTheoremBodyOrigin.lean",
        name="exact_value_origin_not_ci_ledger_artifact",
        required_any=("notCILedgerArtifact",),
    ),
)


def strip_lean_comments(text: str) -> str:
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


def cleaned_source(text: str) -> str:
    return STRING_RE.sub('""', strip_lean_comments(text))


def theorem_block(source: str, name: str) -> str | None:
    pattern = re.compile(THEOREM_RE_TEMPLATE.format(name=re.escape(name)), re.MULTILINE)
    match = pattern.search(source)
    if match is None:
        return None
    return match.group(0)


def iter_lean_files(root: Path):
    for path in root.rglob("*.lean"):
        if any(part in SKIP_DIRS for part in path.parts):
            continue
        yield path


def audit_forbidden_tokens(root: Path) -> list[str]:
    hits: list[str] = []
    for path in iter_lean_files(root):
        source = cleaned_source(path.read_text(encoding="utf-8"))
        for lineno, line in enumerate(source.splitlines(), start=1):
            if FORBIDDEN_TOKENS_RE.search(line):
                hits.append(f"{path}:{lineno}: forbidden token in major-theorem audit")
    return hits


def audit_trivial_true_theorems(root: Path) -> list[str]:
    hits: list[str] = []
    for spec in MAJOR_THEOREMS:
        path = root / spec.path
        source = cleaned_source(path.read_text(encoding="utf-8"))
        for match in TRIVIAL_TRUE_THEOREM_RE.finditer(source):
            theorem_name = match.group(1)
            hits.append(f"{path}: theorem {theorem_name} has trivial True statement")
    return hits


def audit_required_theorems(root: Path) -> list[str]:
    failures: list[str] = []
    for spec in MAJOR_THEOREMS:
        path = root / spec.path
        if not path.exists():
            failures.append(f"missing file: {path}")
            continue
        source = cleaned_source(path.read_text(encoding="utf-8"))
        block = theorem_block(source, spec.name)
        if block is None:
            failures.append(f"missing theorem: {path}:{spec.name}")
            continue
        if ": True :=" in block or ": Prop := True" in block:
            failures.append(f"placeholder theorem statement: {path}:{spec.name}")
        if not any(anchor in block for anchor in spec.required_any):
            failures.append(
                f"theorem lacks required anchor any{spec.required_any}: {path}:{spec.name}"
            )
        missing_all = [anchor for anchor in spec.required_all if anchor not in block]
        if missing_all:
            failures.append(
                f"theorem lacks required anchors {missing_all}: {path}:{spec.name}"
            )
    return failures


def main() -> None:
    root = Path(".")
    failures: list[str] = []
    failures.extend(audit_forbidden_tokens(root))
    failures.extend(audit_trivial_true_theorems(root))
    failures.extend(audit_required_theorems(root))

    print(f"Major theorem specs audited: {len(MAJOR_THEOREMS)}")
    print("Forbidden Lean tokens audited: sorry/admit/axiom/constant")
    print("Trivial theorem statement audit: theorem ... : True :=")
    print("Statement-anchor audit: exact value, positivity, spectralWeight, PVM mass, normalization")

    if failures:
        print("Major theorem non-placeholder audit failed:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        raise SystemExit(1)

    print("Major theorem non-placeholder audit passed")


if __name__ == "__main__":
    main()
