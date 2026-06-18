#!/usr/bin/env python3
"""Summarize Lean feedback episodes and rank repair actions by reward gain."""

from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from pathlib import Path
from statistics import mean
from typing import Any, Sequence


DEFAULT_LEDGER = Path(".lean-feedback/episodes.jsonl")


def _load(path: Path) -> list[dict[str, Any]]:
    episodes: list[dict[str, Any]] = []
    if not path.exists():
        return episodes
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        try:
            value = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(value, dict):
            episodes.append(value)
    return episodes


def summarize(episodes: Sequence[dict[str, Any]]) -> dict[str, Any]:
    categories: Counter[str] = Counter()
    rewards: list[int] = []
    transitions: dict[tuple[str, str], list[int]] = defaultdict(list)
    successes = 0

    for episode in episodes:
        feedback = episode.get("feedback", {})
        category = feedback.get("primary_category")
        reward = feedback.get("reward")
        if isinstance(category, str):
            categories[category] += 1
            if category.startswith("build_success"):
                successes += 1
        if isinstance(reward, int):
            rewards.append(reward)

        action = episode.get("action")
        parent_category = episode.get("parent_category")
        delta = episode.get("transition_reward")
        if isinstance(action, str) and isinstance(parent_category, str) and isinstance(delta, int):
            transitions[(parent_category, action)].append(delta)

    ranked_actions = [
        {
            "parent_category": parent_category,
            "action": action,
            "uses": len(values),
            "mean_transition_reward": mean(values),
            "best_transition_reward": max(values),
        }
        for (parent_category, action), values in transitions.items()
    ]
    ranked_actions.sort(
        key=lambda item: (item["mean_transition_reward"], item["uses"]), reverse=True
    )

    total = len(episodes)
    return {
        "episodes": total,
        "successes": successes,
        "success_rate": successes / total if total else 0.0,
        "mean_reward": mean(rewards) if rewards else 0.0,
        "categories": dict(categories.most_common()),
        "ranked_actions": ranked_actions,
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ledger", type=Path, default=DEFAULT_LEDGER)
    parser.add_argument("--pretty", action="store_true")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    result = summarize(_load(args.ledger))
    print(json.dumps(result, ensure_ascii=False, indent=2 if args.pretty else None, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
