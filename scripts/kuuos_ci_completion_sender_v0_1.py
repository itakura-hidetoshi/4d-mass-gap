#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import re
from typing import Any, Mapping

VERSION = "mgap4d_kuuos_ci_completion_sender_v0_1"
EVENT_TYPE = "kuuos_ci_completion_v1_1"
SOURCE_REPOSITORY = "itakura-hidetoshi/4d-mass-gap"
SOURCE_WORKFLOW = "PR Lean Fast Check"
SOURCE_JOB = "Changed Lean fast check"
SOURCE_STEP = "Run changed Lean fast check"
CANONICAL_BASE = "formal/real-hilbert-uniform-coercive-strong-limit"
DESTINATION_REPOSITORY = "itakura-hidetoshi/KuuOS"

_TERMINAL_CONCLUSIONS = {
    "success",
    "failure",
    "cancelled",
    "timed_out",
    "neutral",
    "skipped",
    "stale",
    "action_required",
    "startup_failure",
}
_SHA40 = re.compile(r"^[0-9a-f]{40}$")


def _m(value: Any) -> Mapping[str, Any]:
    return value if isinstance(value, Mapping) else {}


def _i(value: Any, default: int = 0) -> int:
    if isinstance(value, bool):
        return default
    try:
        return int(value)
    except (TypeError, ValueError):
        return default


def _digest(value: Any) -> str:
    encoded = json.dumps(
        value,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _jobs(payload: Mapping[str, Any]) -> list[Mapping[str, Any]]:
    raw = payload.get("jobs", [])
    if not isinstance(raw, list):
        return []
    return [item for item in raw if isinstance(item, Mapping)]


def _steps(job: Mapping[str, Any]) -> list[Mapping[str, Any]]:
    raw = job.get("steps", [])
    if not isinstance(raw, list):
        return []
    return [item for item in raw if isinstance(item, Mapping)]


def _matching_pr(run: Mapping[str, Any]) -> Mapping[str, Any]:
    raw = run.get("pull_requests", [])
    if not isinstance(raw, list):
        return {}
    for item in raw:
        if not isinstance(item, Mapping):
            continue
        base = _m(item.get("base"))
        head = _m(item.get("head"))
        head_repo = _m(head.get("repo"))
        if (
            str(base.get("ref", "")) == CANONICAL_BASE
            and str(head_repo.get("full_name", SOURCE_REPOSITORY)) == SOURCE_REPOSITORY
        ):
            return item
    return {}


def compile_dispatch(
    event: Mapping[str, Any],
    jobs_payload: Mapping[str, Any],
) -> dict[str, Any]:
    blockers: list[str] = []
    run = _m(event.get("workflow_run"))
    repository = _m(event.get("repository"))
    head_repository = _m(run.get("head_repository"))

    if str(event.get("action", "")) != "completed":
        blockers.append("event_action_not_completed")
    if str(repository.get("full_name", "")) != SOURCE_REPOSITORY:
        blockers.append("repository_mismatch")
    if str(run.get("name", "")) != SOURCE_WORKFLOW:
        blockers.append("workflow_name_mismatch")
    if str(run.get("event", "")) != "pull_request":
        blockers.append("source_run_event_not_pull_request")
    if str(run.get("status", "")) != "completed":
        blockers.append("source_workflow_not_completed")
    if run.get("conclusion") not in _TERMINAL_CONCLUSIONS:
        blockers.append("source_workflow_conclusion_not_terminal")
    if str(head_repository.get("full_name", SOURCE_REPOSITORY)) != SOURCE_REPOSITORY:
        blockers.append("untrusted_head_repository")

    run_id = _i(run.get("id"), 0)
    if run_id <= 0:
        blockers.append("run_id_invalid")
    head_sha = str(run.get("head_sha", "")).lower()
    if _SHA40.fullmatch(head_sha) is None:
        blockers.append("head_sha_invalid")

    pr = _matching_pr(run)
    if not pr:
        blockers.append("canonical_base_pull_request_missing")
    pr_number = _i(pr.get("number"), 0) if pr else 0
    if pr and pr_number <= 0:
        blockers.append("pull_request_number_invalid")

    exact_job: Mapping[str, Any] = {}
    for job in _jobs(jobs_payload):
        if str(job.get("name", "")) == SOURCE_JOB:
            exact_job = job
            break
    if not exact_job:
        blockers.append("required_job_missing")
    elif str(exact_job.get("status", "")) != "completed":
        blockers.append("required_job_not_completed")
    elif exact_job.get("conclusion") not in _TERMINAL_CONCLUSIONS:
        blockers.append("required_job_conclusion_not_terminal")

    exact_step: Mapping[str, Any] = {}
    if exact_job:
        for step in _steps(exact_job):
            if str(step.get("name", "")) == SOURCE_STEP:
                exact_step = step
                break
    if not exact_step:
        blockers.append("required_step_missing")
    elif str(exact_step.get("status", "")) != "completed":
        blockers.append("required_step_not_completed")
    elif exact_step.get("conclusion") not in _TERMINAL_CONCLUSIONS:
        blockers.append("required_step_conclusion_not_terminal")

    client_payload = {
        "version": VERSION,
        "repository": SOURCE_REPOSITORY,
        "run_id": run_id,
        "workflow_name": SOURCE_WORKFLOW,
        "head_sha": head_sha,
        "head_branch": str(run.get("head_branch", "")),
        "status": str(run.get("status", "")),
        "conclusion": run.get("conclusion"),
        "run_event": str(run.get("event", "")),
        "pr_number": pr_number,
        "pr_base_branch": CANONICAL_BASE,
        "required_job_names": [SOURCE_JOB],
        "required_step_names": [SOURCE_STEP],
        "source_job_conclusion": exact_job.get("conclusion") if exact_job else None,
        "source_step_conclusion": exact_step.get("conclusion") if exact_step else None,
        "destination_repository": DESTINATION_REPOSITORY,
        "source_event_digest": _digest(event),
        "source_jobs_digest": _digest(jobs_payload),
        "event_is_wakeup_signal_only": True,
        "fresh_mcp_reobservation_required": True,
    }
    dispatch = {
        "event_type": EVENT_TYPE,
        "client_payload": client_payload,
    }
    return {
        "version": VERSION,
        "status": "MGAP4D_KUUOS_CI_COMPLETION_SENDER_READY"
        if not blockers
        else "MGAP4D_KUUOS_CI_COMPLETION_SENDER_BLOCKED",
        "dispatch_allowed": not blockers,
        "destination_repository": DESTINATION_REPOSITORY,
        "dispatch": dispatch,
        "dispatch_digest": _digest(dispatch),
        "blockers": blockers,
        "boundary": {
            "same_repository_source_required": True,
            "canonical_base_pr_required": True,
            "completed_source_workflow_required": True,
            "exact_job_required": SOURCE_JOB,
            "exact_step_required": SOURCE_STEP,
            "source_event_is_not_success_evidence": True,
            "destination_must_freshly_reobserve_via_mcp": True,
            "sender_grants_no_merge_authority": True,
        },
    }


def _write(path: pathlib.Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(dict(payload), ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def _fixture(*, conclusion: str = "success") -> tuple[dict[str, Any], dict[str, Any]]:
    sha = "a" * 40
    event = {
        "action": "completed",
        "repository": {"full_name": SOURCE_REPOSITORY},
        "workflow_run": {
            "id": 123,
            "name": SOURCE_WORKFLOW,
            "event": "pull_request",
            "status": "completed",
            "conclusion": conclusion,
            "head_sha": sha,
            "head_branch": "formal/example",
            "head_repository": {"full_name": SOURCE_REPOSITORY},
            "pull_requests": [
                {
                    "number": 2009,
                    "base": {"ref": CANONICAL_BASE},
                    "head": {
                        "sha": sha,
                        "repo": {"full_name": SOURCE_REPOSITORY},
                    },
                }
            ],
        },
    }
    jobs = {
        "jobs": [
            {
                "name": SOURCE_JOB,
                "status": "completed",
                "conclusion": conclusion,
                "steps": [
                    {
                        "name": SOURCE_STEP,
                        "status": "completed",
                        "conclusion": conclusion,
                    }
                ],
            }
        ]
    }
    return event, jobs


def self_check() -> None:
    event, jobs = _fixture()
    ready = compile_dispatch(event, jobs)
    assert ready["dispatch_allowed"] is True
    assert ready["dispatch"]["event_type"] == EVENT_TYPE
    assert ready["dispatch"]["client_payload"]["required_step_names"] == [SOURCE_STEP]
    assert ready["dispatch"]["client_payload"]["head_sha"] == "a" * 40

    failed_event, failed_jobs = _fixture(conclusion="failure")
    failed = compile_dispatch(failed_event, failed_jobs)
    assert failed["dispatch_allowed"] is True
    assert failed["dispatch"]["client_payload"]["conclusion"] == "failure"

    wrong_base_event, wrong_base_jobs = _fixture()
    wrong_base_event["workflow_run"]["pull_requests"][0]["base"]["ref"] = "main"
    wrong_base = compile_dispatch(wrong_base_event, wrong_base_jobs)
    assert wrong_base["dispatch_allowed"] is False
    assert "canonical_base_pull_request_missing" in wrong_base["blockers"]

    fork_event, fork_jobs = _fixture()
    fork_event["workflow_run"]["head_repository"]["full_name"] = "someone/fork"
    fork = compile_dispatch(fork_event, fork_jobs)
    assert fork["dispatch_allowed"] is False
    assert "untrusted_head_repository" in fork["blockers"]

    missing_step_event, missing_step_jobs = _fixture()
    missing_step_jobs["jobs"][0]["steps"] = []
    missing_step = compile_dispatch(missing_step_event, missing_step_jobs)
    assert missing_step["dispatch_allowed"] is False
    assert "required_step_missing" in missing_step["blockers"]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-check", action="store_true")
    parser.add_argument("--event")
    parser.add_argument("--jobs-json")
    parser.add_argument("--output", default="kuuos-ci-completion-dispatch.json")
    args = parser.parse_args()

    if args.self_check:
        self_check()
        print("MGAP4D_KUUOS_CI_COMPLETION_SENDER_V0_1_SELF_CHECK_OK")
        return 0

    if not args.event or not args.jobs_json:
        parser.error("--event and --jobs-json are required unless --self-check is used")

    event = json.loads(pathlib.Path(args.event).read_text(encoding="utf-8"))
    jobs = json.loads(pathlib.Path(args.jobs_json).read_text(encoding="utf-8"))
    if not isinstance(event, Mapping) or not isinstance(jobs, Mapping):
        raise SystemExit("event and jobs payloads must be JSON objects")

    result = compile_dispatch(event, jobs)
    _write(pathlib.Path(args.output), result)
    print(result["status"])
    return 0 if result["dispatch_allowed"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
