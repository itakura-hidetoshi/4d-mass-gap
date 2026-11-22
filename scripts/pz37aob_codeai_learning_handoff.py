"""Read-only AOB learning handoff through exact KuuOS-native evaluators.

This adapter submits real observations as context, never as fabricated independent
verifier packets. Direct Lean and Lean MCP from one candidate-producing pipeline
do not establish four independent check families. Missing objects remain None.
The two native evaluators are called even when their honest result is blocked.

Upstream pin: 0dca3cc8a69ef523946a9ad4e07d0cc8f7394925
No network, subprocess, git, gh, mutation, or memory persistence occurs here.
"""
from __future__ import annotations

from dataclasses import asdict
import hashlib
from typing import Any, Mapping

from runtime.kuuos_codeai_candidate_patch_envelope_v0_1 import (
    CANDIDATE_DIGEST_FIELD,
    canonical_digest,
)
from runtime.kuuos_codeai_independent_verifier_ensemble_v0_2 import (
    evaluate_independent_verifier_ensemble,
)
from runtime.kuuos_codeai_independent_verifier_ensemble_checks_v0_2 import seal as ensemble_seal
from runtime.kuuos_codeai_independent_verifier_ensemble_schema_v0_2 import (
    REQUEST_DIGEST_FIELD as ENSEMBLE_REQUEST_DIGEST_FIELD,
    POLICY_DIGEST_FIELD as ENSEMBLE_POLICY_DIGEST_FIELD,
)
from runtime.kuuos_codeai_subtask_level_version_bound_memory_v0_1 import (
    build_codeai_subtask_level_version_bound_memory,
)
from runtime.kuuos_codeai_subtask_level_version_bound_memory_schema_v0_1 import (
    SCHEMA_VERSION as MEMORY_SCHEMA_VERSION,
    PROFILE_VERSION as MEMORY_PROFILE_VERSION,
    REQUEST_DIGEST_FIELD as MEMORY_REQUEST_DIGEST_FIELD,
    POLICY_DIGEST_FIELD as MEMORY_POLICY_DIGEST_FIELD,
    CORPUS_DIGEST_FIELD as MEMORY_CORPUS_DIGEST_FIELD,
    VERSION_BINDING_FIELDS,
    SUBTASK_KINDS,
    OUTCOME_VERIFIED_USEFUL,
    seal as memory_seal,
)

UPSTREAM_PIN = "0dca3cc8a69ef523946a9ad4e07d0cc8f7394925"
REQUIRED_FAMILIES = [
    "adversarial_and_falsification",
    "behavioral_and_regression",
    "maintainability_and_static",
    "type_and_formal",
]


def _digest_or_none(value: Any) -> str | None:
    return None if value is None else canonical_digest(value)


def build_aob_learning_handoff(
    *,
    source_binding: Mapping[str, Any],
    candidate_patch: Mapping[str, Any] | None,
    candidate_source: str | None,
    context_files: Mapping[str, str],
    direct_lean_receipt: Mapping[str, Any] | None,
    lean_mcp_receipt: Mapping[str, Any] | None,
    toolchain_receipt: Mapping[str, Any] | None,
    environment_receipt: Mapping[str, Any] | None,
    observed_epoch: int,
) -> dict[str, Any]:
    """Evaluate the current *incomplete* learning handoff without promotion.

    source_binding must report actual values where known:
      repository_full_name, source_commit_sha, source_tree_sha, source_actor_id,
      runner_id. Unknown identity values must be None; do not invent them.

    candidate_patch is the actual upstream GeneratedUnifiedDiffCandidate.patch_candidate.
    context_files is the actual observed source mapping sent to the generator.

    direct_lean_receipt must contain exit_code and candidate_source_sha256.
    lean_mcp_receipt must contain success, partial, failed_dependencies, items,
    and candidate_source_sha256. The latter fields come from real structured MCP
    output plus a caller-side before/after source identity check.

    This function is intentionally for the stage before independently collected
    verifier evidence or a version-bound memory corpus exists. It always sends
    zero independent packets and an empty memory corpus, preserving absent
    ensemble/temporal-corpus objects as None. Hence native blocked is expected.
    It does not claim a successful native "no_match" when schema prerequisites
    are unavailable.
    """
    if isinstance(observed_epoch, bool) or not isinstance(observed_epoch, int) or observed_epoch <= 0:
        raise ValueError("observed_epoch must be the actual positive observation time")
    if not isinstance(context_files, Mapping) or any(
        not isinstance(path, str) or not isinstance(source, str)
        for path, source in context_files.items()
    ):
        raise ValueError("context_files must contain observed path/text pairs")

    repository = source_binding.get("repository_full_name")
    source_commit = source_binding.get("source_commit_sha")
    source_tree_sha = source_binding.get("source_tree_sha")
    candidate_digest = (
        candidate_patch.get(CANDIDATE_DIGEST_FIELD)
        if candidate_patch is not None else None
    )
    candidate_source_sha256 = (
        hashlib.sha256(candidate_source.encode("utf-8")).hexdigest()
        if candidate_source is not None else None
    )
    context_pack = {
        "kind": "observed_source_context",
        "repository_full_name": repository,
        "source_commit_sha": source_commit,
        "files": [
            {"path": path, "sha256": hashlib.sha256(content.encode("utf-8")).hexdigest()}
            for path, content in sorted(context_files.items())
        ],
    }
    context_digest = canonical_digest(context_pack)
    source_tree_digest = (
        canonical_digest({"git_tree_sha": source_tree_sha})
        if source_tree_sha is not None else None
    )
    candidate_digest_valid = bool(
        candidate_patch is not None
        and candidate_digest is not None
        and candidate_digest == canonical_digest(
            {key: value for key, value in candidate_patch.items() if key != CANDIDATE_DIGEST_FIELD}
        )
        and candidate_patch.get("repository_full_name") == repository
        and candidate_patch.get("source_commit_sha") == source_commit
    )

    direct = dict(direct_lean_receipt) if direct_lean_receipt is not None else None
    mcp = dict(lean_mcp_receipt) if lean_mcp_receipt is not None else None
    direct_bound = bool(
        direct is not None and candidate_source_sha256 is not None
        and direct.get("candidate_source_sha256") == candidate_source_sha256
    )
    mcp_bound = bool(
        mcp is not None and candidate_source_sha256 is not None
        and mcp.get("candidate_source_sha256") == candidate_source_sha256
    )
    direct_audit = direct.get("audit") if direct is not None else None
    direct_passed = bool(
        direct_bound and type(direct.get("exit_code")) is int
        and direct["exit_code"] == 0
        and isinstance(direct_audit, Mapping)
        and isinstance(direct_audit.get("audited_declarations"), list)
        and bool(direct_audit["audited_declarations"])
        and direct_audit.get("warning_count") == 0
        and direct_audit.get("error_count") == 0
        and direct_audit.get("sorryAx") is False
    )
    mcp_items = mcp.get("items") if mcp is not None else None
    mcp_passed = bool(
        mcp_bound and mcp.get("success") is True and mcp.get("partial") is False
        and mcp.get("timed_out") is not True
        and mcp.get("failed_dependencies") == []
        and isinstance(mcp_items, list)
        and all(isinstance(item, Mapping) and item.get("severity") in
                {"error", "warning", "info", "hint"} for item in mcp_items)
        and not any(item.get("severity") in {"error", "warning"} for item in mcp_items)
    )

    # These are actual observed method names and allowlists, not invented
    # evidence identities. An absent actor or runner makes the policy invalid;
    # it is not filled with a synthetic "independent reviewer".
    actor_id = source_binding.get("source_actor_id")
    runner_id = source_binding.get("runner_id")
    ensemble_request = ensemble_seal({
        "request_id": "aob-observed-lean-learning-handoff",
        "request_revision": "r1",
        "repository_full_name": repository,
        "source_commit_sha": source_commit,
        "candidate_digest": candidate_digest,
        "context_pack_digest": context_digest,
        "required_check_families": REQUIRED_FAMILIES,
        "request_created_epoch": observed_epoch,
    }, ENSEMBLE_REQUEST_DIGEST_FIELD)
    ensemble_policy = ensemble_seal({
        "expected_repository_full_name": repository,
        "expected_source_commit_sha": source_commit,
        "expected_candidate_digest": candidate_digest,
        "expected_context_pack_digest": context_digest,
        "allowed_verifier_ids": ["direct-lean", "lean-lsp-mcp"],
        "allowed_reviewer_ids": [actor_id] if isinstance(actor_id, str) and actor_id else [],
        "allowed_runner_ids": [runner_id] if isinstance(runner_id, str) and runner_id else [],
        "required_check_families": REQUIRED_FAMILIES,
        "minimum_verifier_count": 4,
        "minimum_organization_count": 4,
        "minimum_method_count": 4,
        "minimum_pass_quorum": 3,
        "minimum_fail_quorum": 2,
        "maximum_skipped_checks": 0,
        "maximum_evidence_age": 3600,
        "maximum_verification_duration": 1800,
        "evaluation_epoch": observed_epoch,
        "require_distinct_verifiers": True,
        "require_distinct_sessions": True,
        "require_distinct_organizations": True,
        "require_producer_independence": True,
        "require_peer_independence": True,
        "require_prompt_independence": True,
        "require_memory_independence": True,
        "require_test_generation_independence": True,
        "critical_failure_overrides_quorum": True,
        "conflict_requires_hold": True,
        "allow_repository_mutation": False,
        "allow_network_access": False,
        "allow_secret_access": False,
        "allow_candidate_selection_authority": False,
        "allow_execution_authority": False,
        "allow_git_authority": False,
    }, ENSEMBLE_POLICY_DIGEST_FIELD)

    independent_packets: list[dict[str, Any]] = []
    ensemble_result = evaluate_independent_verifier_ensemble(
        ensemble_request, ensemble_policy, independent_packets
    )

    # Neither a blocked-result hash nor a constant HOLD hash is an ensemble.
    # Missing ensemble/temporal corpus remain None in the actual native request.
    binding = {
        "repository_full_name": repository,
        "source_commit_sha": source_commit,
        "source_tree_digest": source_tree_digest,
        "temporal_corpus_digest": None,
        "context_pack_digest": context_digest,
        "verifier_ensemble_digest": None,
        "subtask_kind": "verify",
        "subtask_contract_digest": canonical_digest({
            "subtask": "verify", "requires": ["exact_candidate_source", "direct_lean",
            "real_lean_mcp", "independent_verifier_ensemble", "holdout_protection"],
        }),
        "predecessor_output_digest": candidate_digest,
        "dependency_slice_digest": canonical_digest(context_pack["files"]),
        "toolchain_digest": _digest_or_none(toolchain_receipt),
        "environment_digest": _digest_or_none(environment_receipt),
        "memory_policy_digest": canonical_digest({
            "outcome": "verified_useful_only",
            "exact_binding_required": True,
            "missing_evidence": "HOLD",
        }),
    }
    unresolved = [
        "independent_verifier_ensemble_absent",
        "temporal_holdout_corpus_absent",
        "version_bound_memory_corpus_absent",
    ]
    memory_request = memory_seal({
        "schema_version": MEMORY_SCHEMA_VERSION,
        "profile_version": MEMORY_PROFILE_VERSION,
        "request_id": "aob-subtask-memory-readonly-query",
        "request_revision": "r1",
        **binding,
        "request_created_epoch": observed_epoch,
        "unresolved_questions": unresolved,
        "claims_selection_authority": False,
        "claims_repair_authority": False,
        "claims_execution_authority": False,
        "claims_git_authority": False,
    }, MEMORY_REQUEST_DIGEST_FIELD)
    memory_policy = memory_seal({
        "schema_version": MEMORY_SCHEMA_VERSION,
        "profile_version": MEMORY_PROFILE_VERSION,
        **{"expected_" + field: binding[field] for field in VERSION_BINDING_FIELDS},
        "evaluation_epoch": observed_epoch,
        "maximum_request_age": 3600,
        "maximum_entry_age": 86400,
        "maximum_corpus_entries": 16,
        "maximum_matched_entries": 4,
        "allowed_outcomes": [OUTCOME_VERIFIED_USEFUL],
        "required_subtask_kinds": list(SUBTASK_KINDS),
        "require_exact_version_binding": True,
        "require_subtask_alignment": True,
        "require_dependency_alignment": True,
        "require_verifier_grounding": True,
        "require_holdout_protection": True,
        "require_not_superseded": True,
        "allow_memory_hint": True,
        "allow_repository_mutation": False,
        "allow_candidate_selection": False,
        "allow_repair_execution": False,
        "allow_execution_authority": False,
        "allow_git_authority": False,
    }, MEMORY_POLICY_DIGEST_FIELD)
    memory_corpus = memory_seal({
        "schema_version": MEMORY_SCHEMA_VERSION,
        "profile_version": MEMORY_PROFILE_VERSION,
        "corpus_id": "aob-empty-observed-memory-corpus",
        "corpus_revision": "r1",
        "repository_full_name": repository,
        "temporal_corpus_digest": None,
        "context_pack_digest": context_digest,
        "verifier_ensemble_digest": None,
        "entries": [],
    }, MEMORY_CORPUS_DIGEST_FIELD)
    memory_result = build_codeai_subtask_level_version_bound_memory(
        request=memory_request, policy=memory_policy, corpus=memory_corpus
    )

    return {
        "schema_version": "aob-learning-handoff-v1",
        "upstream_codeai_pin": UPSTREAM_PIN,
        "source_binding": dict(source_binding),
        "candidate_digest": candidate_digest,
        "candidate_digest_binding_valid": candidate_digest_valid,
        "candidate_source_sha256": candidate_source_sha256,
        "context_pack": context_pack,
        "context_pack_digest": context_digest,
        "context_path_count": len(context_files),
        "observed_checks": {
            "direct_lean": direct, "lean_mcp": mcp,
            "direct_source_binding_valid": direct_bound,
            "mcp_source_binding_valid": mcp_bound,
            "direct_lean_passed": direct_passed,
            "real_lean_mcp_passed": mcp_passed,
            "observed_method_count": int(direct is not None) + int(mcp is not None),
            "successful_observed_check_count": int(direct_passed) + int(mcp_passed),
            "independent_evidence_count": 0,
            "qualified_independent_families": [],
            "missing_independent_families": REQUIRED_FAMILIES,
        },
        "native_ensemble": {
            "request": ensemble_request, "policy": ensemble_policy,
            "evidence_packets": independent_packets,
            "result": asdict(ensemble_result),
        },
        "native_subtask_memory": {
            "request": memory_request, "policy": memory_policy,
            "corpus": memory_corpus, "result": asdict(memory_result),
            "verified_useful_entries_in_submitted_corpus": 0,
            "matched_entry_count": None,
            "query_disposition": "BLOCKED_MISSING_PREREQUISITES",
        },
        "disposition": "HOLD",
        "hold_reasons": [
            "direct_lean_and_mcp_are_not_independent_ensemble_evidence",
            *unresolved,
        ],
        "verified_useful_promotion_performed": False,
        "memory_read_only": True,
        "repository_mutation_performed": False,
        "candidate_selected_by_learning_handoff": False,
        "execution_authority_granted": False,
        "git_authority_granted": False,
    }
