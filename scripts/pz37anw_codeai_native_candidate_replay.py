#!/usr/bin/env python3
"""Read-only KuuOS-native CodeAI v0.61-path candidate replay for PZ37ANW.

This calls the upstream CodeAI generator from a SHA-pinned KuuOS checkout.
The two deterministic provider responses are authored proposals, NOT live
model inference. No candidate selection, mutation, or proof certification.
"""
import hashlib
import json
import os
import time
from pathlib import Path
from urllib.request import Request, urlopen

from runtime.kuuos_codeai_candidate_patch_envelope_v0_1 import (
    SOURCE_RECEIPT_DIGEST_FIELD, POLICY_DIGEST_FIELD as PATCH_POLICY_DIGEST_FIELD,
    canonical_digest, seal,
)
from runtime.kuuos_codeai_autonomous_structured_edit_synthesis_v0_1 import (
    ProviderAdapter, REQUEST_DIGEST_FIELD, POLICY_DIGEST_FIELD,
    build_codeai_autonomous_structured_edit_synthesis,
)

KUUOS_PIN = "b0201811d176bf25fb50146d380def6fa2e90fa7"
REPOSITORY = "itakura-hidetoshi/4d-mass-gap"
FAILED_HEAD = "85cb3f2e5a483cb7665ea246f20abbb60c81e9ca"
FAILED_TREE = "fff94f7bbbe2e5ad1fd6a07c275c41d32a2c1185"
PATH = "MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFirstHaarSlopeSignV5_PZ37ANW.lean"
OLD = """  have habs : |b + beta * (1 / 4 : ℝ)| < beta * (1 / 4 : ℝ) :=
    (mul_lt_mul_left (sq_pos_of_pos hlambda)).mp hstrict"""
ALTERNATIVE = """  have habs : |b + beta * (1 / 4 : ℝ)| < beta * (1 / 4 : ℝ) := by
    by_contra hn
    have hle : beta * (1 / 4 : ℝ) ≤ |b + beta * (1 / 4 : ℝ)| :=
      le_of_not_gt hn
    exact (not_le_of_gt hstrict)
      (mul_le_mul_of_nonneg_left hle (sq_nonneg lambda))"""


def main():
    now = int(time.time())
    url = "https://raw.githubusercontent.com/" + REPOSITORY + "/" + FAILED_HEAD + "/" + PATH
    with urlopen(Request(url, headers={"User-Agent": "KuuOS-CodeAI-ANW-ReadOnly"}), timeout=30) as resp:
        failed_source = resp.read().decode("utf-8")
    current_source = Path(PATH).read_text(encoding="utf-8")
    assert failed_source.count(OLD) == 1
    start, end = failed_source.split(OLD)
    assert current_source.startswith(start) and current_source.endswith(end)
    assert OLD not in current_source

    pin = Path(os.environ["KUUOS_CODEAI_PINNED_ROOT"])
    fixture = json.loads((pin / "examples/codeai_candidate_patch_envelope_v0_1.json").read_text())
    source = dict(fixture["source_observation_receipt"])
    source.update(
        repository_full_name=REPOSITORY, source_commit_sha=FAILED_HEAD,
        resulting_commit_sha=FAILED_HEAD, tree_digest=FAILED_TREE,
        source_branch="research/p4-q2-pz37-anw-native-top-first-signed-small-coupling-20261122",
        intent_id="PZ37ANW-CODEAI-TYPED-ERROR", intent_revision="r1",
        intent_packet_digest=canonical_digest({"intent": "repair ANW MulRightStrictMono error"}),
        repository_observation_digest=canonical_digest({
            "path": PATH, "sha256": hashlib.sha256(failed_source.encode()).hexdigest(),
            "commit": FAILED_HEAD,
        }),
        observation_policy_digest=canonical_digest({"read_only": True, "path": PATH}),
        observed_path_count=1, declared_path_count=1, unavailable_path_count=0,
    )
    source = seal(source, SOURCE_RECEIPT_DIGEST_FIELD)
    patch_policy = dict(fixture["candidate_policy"])
    patch_policy.update(
        expected_source_observation_receipt_digest=source[SOURCE_RECEIPT_DIGEST_FIELD],
        expected_repository_full_name=REPOSITORY, expected_source_commit_sha=FAILED_HEAD,
        allowed_path_prefixes=["MGAP4D/MathlibAnalytic"], forbidden_path_prefixes=[],
        maximum_changed_paths=1, allow_evidence_degradation=False,
        known_risk_labels=["formal_proof", "documentation", "release", "security"],
        evaluation_epoch=now,
    )
    patch_policy = seal(patch_policy, PATCH_POLICY_DIGEST_FIELD)
    req = seal({
        "request_id": "PZ37ANW-exact-typeclass-error-replay", "request_revision": "r1",
        "intent_text": "Repair the diagnosed ANW Lean MulRightStrictMono class error; preserve all theorem statements.",
        "candidate_count": 3, "request_created_epoch": now,
        "requirement_trace_ids": ["ANW:line117", "CI:44950938534"],
        "test_plan_ids": ["Lean:4.30.0-rc2", "mathlib:5450b53e5ddc75d46418fabb605edbf36bd0beb6", "independent-CI"],
        "risk_labels": ["formal_proof"], "unresolved_candidate_questions": [],
        "prior_candidate_digests": [], "prior_producer_session_ids": [],
    }, REQUEST_DIGEST_FIELD)
    policy = seal({
        "allowed_provider_ids": ["local_model"], "maximum_provider_calls": 3,
        "maximum_raw_output_bytes": 30000, "maximum_intent_bytes": 30000,
        "maximum_repository_snapshot_bytes": 200000, "maximum_proposals": 3,
        "evaluation_epoch": now, "maximum_response_age": 3600, "maximum_request_age": 3600,
        "allowed_repository_path_prefixes": ["MGAP4D/MathlibAnalytic"],
        "forbidden_repository_path_prefixes": [],
    }, POLICY_DIGEST_FIELD)

    def make_adapter(label, new_text, claims=False):
        proposal = {
            "proposal_id": "ANW-typed-"+label, "candidate_revision": "r1",
            "edits": [{"path": PATH, "operation": "modify", "new_content": new_text}],
            "risk_labels": ["formal_proof"], "unresolved_candidate_questions": [],
        }
        response = {
            "provider_response_id": "ANW-response-"+label,
            "producer_session_id": "ANW-session-"+label,
            "response_created_epoch": now,
            "raw_output": json.dumps(proposal, ensure_ascii=False, separators=(",", ":")),
            "claims_authority": claims, "hides_uncertainty": False,
            "bypasses_governance": False, "evidence_missing": False,
        }
        return ProviderAdapter("anw-"+label, "local_model", "deterministic-scripted-"+label,
                               lambda _prompt, r=response: r)
    adapters = [
        make_adapter("A", current_source),
        make_adapter("B", failed_source.replace(OLD, ALTERNATIVE)),
        make_adapter("C", failed_source, claims=True),
    ]
    result = build_codeai_autonomous_structured_edit_synthesis(
        source_observation_receipt=source, repository_files={PATH: failed_source},
        synthesis_request=req, provider_adapters=adapters,
        synthesis_policy=policy, candidate_policy=patch_policy,
    )
    artifact = {
        "upstream_codeai": KUUOS_PIN, "failed_head": FAILED_HEAD,
        "current_head": os.getenv("ANW_HEAD", "unknown"),
        "status": result.status, "issues": list(result.issues),
        "attempts": [a.__dict__ for a in result.attempts],
        "candidates": [
            {"rank": c.rank, "proposal_id": c.proposal_id,
             "sha256_of_diff": hashlib.sha256(c.patch_artifact.encode()).hexdigest(),
             "candidate_patch": c.patch_candidate,
             "receipt": c.candidate_receipt,
             "state": "TEST_REQUIRED"} for c in result.candidates
        ],
        "synthesis_receipt": result.receipt,
        "lean_certification": "NOT_GRANTED_BY_CODEAI",
        "memory_promotion": "HOLD",
        "repository_modified_by_replay": False,
    }
    out = Path(os.environ.get("RUNNER_TEMP", "/tmp")) / "anw-codeai-native.json"
    out.write_text(json.dumps(artifact, ensure_ascii=False, indent=2, sort_keys=True)+"\n")
    print(json.dumps({"status": result.status, "issues": result.issues,
        "attempt_boundaries": [a.boundary_status for a in result.attempts],
        "candidates": len(result.candidates), "artifact": str(out)}, ensure_ascii=False))
    assert result.status == "ready", result.issues
    assert len(result.candidates) == 2
    assert [a.boundary_status for a in result.attempts] == ["CANDIDATE", "CANDIDATE", "REJECT"]
    assert result.receipt and result.receipt["candidate_selected"] is False
    assert result.receipt["execution_authority_granted"] is False
    assert result.receipt["repository_mutation_performed"] is False


if __name__ == "__main__":
    main()
