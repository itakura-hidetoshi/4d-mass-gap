#!/usr/bin/env python3
"""Run a targeted Lake build and append a reinforcement-learning episode.

An episode records the exact target, toolchain, Git state, compiler feedback,
and reward. When --action is supplied, the latest episode for the same target
is used as the parent unless --parent is explicit; the reward delta then measures
whether that repair action improved the compiler state.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
import time
import uuid
from pathlib import Path
from typing import Any, Sequence

from lean_feedback_classifier import classify_text


DEFAULT_LEDGER = Path(".lean-feedback/episodes.jsonl")


def _run(command: Sequence[str]) -> tuple[int, str]:
    try:
        completed = subprocess.run(
            list(command),
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            encoding="utf-8",
            errors="replace",
            check=False,
        )
    except OSError as error:
        return 127, f"lake error: unable to execute {command[0]!r}: {error}\n"
    return completed.returncode, completed.stdout


def _read_text(path: Path) -> str | None:
    try:
        return path.read_text(encoding="utf-8").strip()
    except OSError:
        return None


def _git_value(*args: str) -> str | None:
    try:
        completed = subprocess.run(
            ["git", *args],
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            text=True,
            check=False,
        )
    except OSError:
        return None
    value = completed.stdout.strip()
    return value if completed.returncode == 0 and value else None


def _load_ledger(path: Path) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    episodes: list[dict[str, Any]] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        try:
            item = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(item, dict):
            episodes.append(item)
    return episodes


def _find_parent(
    episodes: Sequence[dict[str, Any]], targets: Sequence[str], parent_id: str | None
) -> dict[str, Any] | None:
    if parent_id:
        return next((episode for episode in episodes if episode.get("episode_id") == parent_id), None)
    normalized = list(targets)
    return next(
        (episode for episode in reversed(episodes) if episode.get("targets") == normalized),
        None,
    )


def _digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8", errors="replace")).hexdigest()


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("targets", nargs="+", help="Lake build targets")
    parser.add_argument("--lake", default="lake", help="Lake executable")
    parser.add_argument("--ledger", type=Path, default=DEFAULT_LEDGER)
    parser.add_argument("--log-dir", type=Path, default=Path(".lean-feedback/logs"))
    parser.add_argument("--action", default=None, help="Repair action applied since the parent episode")
    parser.add_argument("--parent", default=None, help="Explicit parent episode id")
    parser.add_argument("--note", default=None, help="Optional short note for later analysis")
    parser.add_argument("--no-ledger", action="store_true", help="Run and classify without writing files")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    command = [args.lake, "build", *args.targets]
    started_ns = time.time_ns()
    exit_code, output = _run(command)
    finished_ns = time.time_ns()
    feedback = classify_text(output, exit_code=exit_code)

    previous_episodes = [] if args.no_ledger else _load_ledger(args.ledger)
    parent = None
    if args.action or args.parent:
        parent = _find_parent(previous_episodes, args.targets, args.parent)
        if args.parent and parent is None:
            print(f"unknown parent episode: {args.parent}", file=sys.stderr)
            return 2

    episode_id = uuid.uuid4().hex[:16]
    transition_reward = None
    parent_id = None
    parent_category = None
    if parent is not None:
        parent_id = parent.get("episode_id")
        parent_category = parent.get("feedback", {}).get("primary_category")
        old_reward = parent.get("feedback", {}).get("reward")
        if isinstance(old_reward, int):
            transition_reward = feedback.reward - old_reward

    record: dict[str, Any] = {
        "schema_version": 1,
        "episode_id": episode_id,
        "timestamp_unix_ns": started_ns,
        "duration_ms": round((finished_ns - started_ns) / 1_000_000, 3),
        "command": command,
        "targets": list(args.targets),
        "exit_code": exit_code,
        "toolchain": _read_text(Path("lean-toolchain")),
        "git_head": _git_value("rev-parse", "HEAD"),
        "git_branch": _git_value("rev-parse", "--abbrev-ref", "HEAD"),
        "git_status": _git_value("status", "--porcelain"),
        "log_sha256": _digest(output),
        "feedback": feedback.to_dict(),
        "action": args.action,
        "parent_episode_id": parent_id,
        "parent_category": parent_category,
        "transition_reward": transition_reward,
        "note": args.note,
    }

    if not args.no_ledger:
        args.log_dir.mkdir(parents=True, exist_ok=True)
        log_path = args.log_dir / f"{episode_id}.log"
        log_path.write_text(output, encoding="utf-8")
        record["log_path"] = str(log_path)
        args.ledger.parent.mkdir(parents=True, exist_ok=True)
        with args.ledger.open("a", encoding="utf-8") as handle:
            handle.write(json.dumps(record, ensure_ascii=False, sort_keys=True) + "\n")

    summary = {
        "episode_id": episode_id,
        "category": feedback.primary_category,
        "reward": feedback.reward,
        "transition_reward": transition_reward,
        "advice": feedback.advice,
        "exit_code": exit_code,
    }
    print(json.dumps(summary, ensure_ascii=False, indent=2, sort_keys=True))
    if output:
        sys.stdout.write("\n--- lake output ---\n")
        sys.stdout.write(output)
        if not output.endswith("\n"):
            sys.stdout.write("\n")
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
