#!/usr/bin/env python3
"""Classify Lean/mathlib build output into stable feedback categories.

The classifier is intentionally dependency-free so it can run before Lake or
Mathlib caches are available. It converts compiler feedback into a small,
version-controlled reward signal suitable for iterative proof repair.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Sequence


@dataclass(frozen=True)
class FeedbackRule:
    category: str
    reward: int
    advice: str
    patterns: tuple[str, ...]


@dataclass(frozen=True)
class FeedbackMatch:
    category: str
    reward: int
    advice: str
    pattern: str
    count: int


@dataclass(frozen=True)
class Feedback:
    primary_category: str
    reward: int
    advice: str
    exit_code: int | None
    matches: tuple[FeedbackMatch, ...]

    def to_dict(self) -> dict[str, object]:
        result = asdict(self)
        result["matches"] = [asdict(match) for match in self.matches]
        return result


# Earlier rules have higher diagnostic priority when several layers fail in the
# same build. This reflects Lean's processing order: syntax before elaboration,
# elaboration before tactics/kernel acceptance.
RULES: tuple[FeedbackRule, ...] = (
    FeedbackRule(
        "placeholder",
        -100,
        "Remove sorry/admit/placeholders and rebuild; only kernel-checked proofs are positive examples.",
        (
            r"declaration uses ['`]?sorry",
            r"contains ['`]?sorry",
            r"\bsorryAx\b",
            r"\badmit\b",
        ),
    ),
    FeedbackRule(
        "parser",
        -8,
        "Repair tokens, binders, delimiters, or unsupported identifier syntax before changing the mathematics.",
        (
            r"unexpected token",
            r"unexpected end of input",
            r"invalid syntax",
            r"expected (?:term|token|identifier|command)",
            r"parser error",
        ),
    ),
    FeedbackRule(
        "auto_implicit",
        -6,
        "Declare every variable and type parameter explicitly under -DautoImplicit=false.",
        (
            r"autoImplicit",
            r"implicit variable declaration has been disabled",
            r"unknown identifier.*(?:type|variable|parameter)",
        ),
    ),
    FeedbackRule(
        "name_resolution",
        -6,
        "Check imports, namespaces, exact theorem names, and fully qualified declarations with #check/#print.",
        (
            r"unknown identifier",
            r"unknown constant",
            r"unknown namespace",
            r"invalid field notation",
            r"invalid field",
            r"ambiguous.*identifier",
        ),
    ),
    FeedbackRule(
        "typeclass",
        -5,
        "Expose the missing assumptions or instances explicitly; avoid adding broad global instances.",
        (
            r"failed to synthesize",
            r"type class instance problem is stuck",
            r"failed to infer instance",
            r"synthInstance.*failed",
        ),
    ),
    FeedbackRule(
        "elaboration",
        -4,
        "Inspect inferred types and argument order; add local type annotations or explicit named arguments.",
        (
            r"application type mismatch",
            r"type mismatch",
            r"invalid argument name",
            r"function expected at",
            r"declaration has metavariables",
            r"don't know how to synthesize placeholder",
            r"cannot synthesize synthetic opaque",
            r"failed to unify",
        ),
    ),
    FeedbackRule(
        "tactic",
        -3,
        "Reduce to the first unsolved goal and prefer explicit have/calc/rw/exact steps before broad automation.",
        (
            r"unsolved goals",
            r"tactic .* failed",
            r"no goals to be solved",
            r"rewrite tactic failed",
            r"simp made no progress",
            r"case .* is not reachable",
        ),
    ),
    FeedbackRule(
        "import_build",
        -2,
        "Verify the module path, toolchain, lake-manifest, and the smallest build target before proof edits.",
        (
            r"unknown module prefix",
            r"bad import",
            r"object file .* does not exist",
            r"failed to build",
            r"lake.*error",
            r"missing manifest",
        ),
    ),
)

WARNING_PATTERNS: tuple[str, ...] = (
    r"\bwarning:\b",
    r"declaration uses ['`]?sorry",
)

SUCCESS_PATTERNS: tuple[str, ...] = (
    r"build completed successfully",
    r"finished successfully",
    r"^success$",
)


def _count(pattern: str, text: str) -> int:
    return len(re.findall(pattern, text, flags=re.IGNORECASE | re.MULTILINE))


def classify_text(text: str, exit_code: int | None = None) -> Feedback:
    """Classify a combined Lean/Lake log.

    The first matched rule is the primary category. All matched categories are
    returned so downstream reports can distinguish a parser cascade from later
    elaboration or tactic diagnostics.
    """

    matches: list[FeedbackMatch] = []
    for rule in RULES:
        for pattern in rule.patterns:
            count = _count(pattern, text)
            if count:
                matches.append(
                    FeedbackMatch(
                        category=rule.category,
                        reward=rule.reward,
                        advice=rule.advice,
                        pattern=pattern,
                        count=count,
                    )
                )
                break

    if matches:
        primary = matches[0]
        return Feedback(
            primary_category=primary.category,
            reward=primary.reward,
            advice=primary.advice,
            exit_code=exit_code,
            matches=tuple(matches),
        )

    warning_count = sum(_count(pattern, text) for pattern in WARNING_PATTERNS)
    if exit_code == 0 or any(_count(pattern, text) for pattern in SUCCESS_PATTERNS):
        advice = (
            "Build succeeded. Preserve this proof shape as a positive example and run the relevant regression target."
        )
        reward = 8 if warning_count == 0 else 6
        category = "build_success" if warning_count == 0 else "build_success_with_warning"
        return Feedback(category, reward, advice, exit_code, tuple())

    if warning_count:
        return Feedback(
            "warning_only",
            -1,
            "Resolve warnings before promoting the proof shape to a reusable positive example.",
            exit_code,
            tuple(),
        )

    return Feedback(
        "unknown_failure",
        -1 if exit_code not in (None, 0) else 0,
        "Retain the raw log and inspect the earliest error line; add a narrow classifier rule only after confirmation.",
        exit_code,
        tuple(),
    )


def _read_inputs(paths: Sequence[str]) -> str:
    if not paths:
        return sys.stdin.read()
    chunks: list[str] = []
    for raw_path in paths:
        path = Path(raw_path)
        chunks.append(path.read_text(encoding="utf-8", errors="replace"))
    return "\n".join(chunks)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("logs", nargs="*", help="Lean/Lake log files; stdin is used when omitted")
    parser.add_argument("--exit-code", type=int, default=None, help="Exit code of the build command")
    parser.add_argument("--pretty", action="store_true", help="Pretty-print JSON")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    feedback = classify_text(_read_inputs(args.logs), exit_code=args.exit_code)
    json.dump(
        feedback.to_dict(),
        sys.stdout,
        ensure_ascii=False,
        indent=2 if args.pretty else None,
        sort_keys=True,
    )
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
