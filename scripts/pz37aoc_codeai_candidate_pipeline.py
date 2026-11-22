#!/usr/bin/env python3
"""Source-bound AOC proposals through real pinned KuuOS CodeAI and Lean MCP.

Strategies are newly authored deterministic proof inputs, not live model calls.
Only emitted CodeAI candidate bytes are tested. No repository writes or merges
are performed by CodeAI; temporary candidate files live in the CI checkout.
"""
from __future__ import annotations

import argparse
from dataclasses import asdict
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
import uuid

KUUOS_PIN = "79bd475296a7e161f09953939ba78c7a2280c1b7"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = re.compile(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b|debug\.skipKernelTC")
AUXILIARY_CONTEXT_PATH = (
    "MGAP4D/MathlibAnalytic/"
    "PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumLocalHarnack.lean"
)
AUXILIARY_GIT_BLOB = "26867ad34c6a9f6e2f7ae25f7b6a388db4606870"
AUXILIARY_SHA256 = "f804e7cd061a142a953e27657890d78bcbe782eaa1fa87465cb529ec89055d24"
AUXILIARY_DIGEST_FIELD = "aoc_auxiliary_source_digest"
PROJECTION_DIGEST_FIELD = "aoc_source_projection_digest"


def sha256(value: bytes | str) -> str:
    return hashlib.sha256(value.encode() if isinstance(value, str) else value).hexdigest()


def require_exact_source(path: Path, expected: str) -> bytes:
    source = path.read_bytes()
    if sha256(source) != expected:
        raise ValueError("exact candidate source changed")
    return source


def audit_lean_output(text: str, exit_code: int, declarations: list[str]) -> dict:
    if type(exit_code) is not int or exit_code != 0:
        raise ValueError("Lean exit status is not zero")
    if re.search(r"\b(?:warning|error):", text):
        raise ValueError("Lean diagnostic is not clean")
    found = {}
    for name, names in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text):
        axioms = {item.strip() for item in names.split(",") if item.strip()}
        if not axioms <= STANDARD_AXIOMS:
            raise ValueError("nonstandard axiom dependency")
        found[name] = sorted(axioms)
    for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
        found[name] = []
    if any(name not in found for name in declarations):
        raise ValueError("missing complete axiom print")
    return {"audited_declarations": declarations,
            "axioms": {name: found[name] for name in declarations},
            "warning_count": 0, "error_count": 0, "sorryAx": False}


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n")


def verify_original_lean_tree(root: Path, expected_tree: str, allowed_new_path: str) -> int:
    """Compute the original MGAP4D Git tree directly, without invoking git."""
    count = 0

    def object_digest(kind: bytes, body: bytes) -> bytes:
        return hashlib.sha1(kind + b" " + str(len(body)).encode() + b"\0" + body).digest()

    def tree(directory: Path) -> bytes:
        nonlocal count
        entries = []
        for item in directory.iterdir():
            if str(item.relative_to(root)) == allowed_new_path:
                continue
            if item.is_symlink():
                raise ValueError("baseline source tree contains unexpected symlink")
            if item.is_dir():
                mode, digest, key = b"40000", tree(item), item.name.encode() + b"/"
            else:
                if item.stat().st_mode & 0o111:
                    raise ValueError("baseline source mode changed")
                mode, digest, key = b"100644", object_digest(b"blob", item.read_bytes()), item.name.encode()
                count += 1
            entries.append((key, mode + b" " + item.name.encode() + b"\0" + digest))
        body = b"".join(entry for _, entry in sorted(entries))
        return object_digest(b"tree", body)

    if tree(root / "MGAP4D").hex() != expected_tree:
        raise ValueError("baseline MGAP4D tree mismatch: changed, missing or unaccounted source")
    return count


def run_captured(command: list[str], cwd: Path, timeout: float) -> dict:
    try:
        result = subprocess.run(command, cwd=cwd, capture_output=True, text=True, timeout=timeout)
        return {"exit_code": result.returncode, "complete": True,
                "stdout": result.stdout, "stderr": result.stderr}
    except subprocess.TimeoutExpired as exc:
        def text(value):
            return value.decode("utf-8", errors="replace") if isinstance(value, bytes) else value or ""
        return {"exit_code": None, "complete": False, "status": "timeout",
                "stdout": text(exc.stdout), "stderr": text(exc.stderr)}


def snapshot(root: Path, pack: dict) -> dict[str, str]:
    files = {}
    for path, expected_blob in pack["baseline_blobs"].items():
        raw = (root / path).read_bytes()
        blob = hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()
        if blob != expected_blob:
            raise ValueError("immutable baseline blob mismatch: " + path)
        files[path] = raw.decode("utf-8")
    if files["lean-toolchain"].strip() != "leanprover/lean4:v4.30.0-rc2":
        raise ValueError("Lean pin changed")
    manifest = json.loads(files["lake-manifest.json"])
    mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
    if mathlib["rev"] != "5450b53e5ddc75d46418fabb605edbf36bd0beb6":
        raise ValueError("mathlib pin changed")
    return files


def prepare_native_context(raw_files: dict[str, str], pack: dict) -> tuple[dict, dict, dict]:
    """Represent one exact no-final-LF dependency without altering its bytes.

    The native patch snapshot has six canonical files. The complete seventh
    source is carried separately as sealed read-only JSON in request intent.
    No other noncanonical path or source revision receives this treatment.
    """
    from runtime.kuuos_codeai_autonomous_structured_edit_types_v0_1 import canonical_text
    from runtime.kuuos_codeai_candidate_patch_envelope_v0_1 import canonical_digest, seal

    if set(raw_files) != set(pack["baseline_blobs"]):
        raise ValueError("raw source context and observed baseline paths differ")
    if pack.get("local_harnack_path") != AUXILIARY_CONTEXT_PATH or AUXILIARY_CONTEXT_PATH not in raw_files:
        raise ValueError("exact auxiliary source path is required")
    for path, content in raw_files.items():
        if not isinstance(content, str):
            raise ValueError("raw source context must contain UTF-8 text")
        encoded = content.encode("utf-8")
        blob = hashlib.sha1(b"blob " + str(len(encoded)).encode() + b"\0" + encoded).hexdigest()
        if blob != pack["baseline_blobs"][path]:
            raise ValueError("immutable raw context blob mismatch: " + path)
    raw = raw_files[AUXILIARY_CONTEXT_PATH]
    encoded = raw.encode("utf-8")
    if (
        pack["baseline_blobs"][AUXILIARY_CONTEXT_PATH] != AUXILIARY_GIT_BLOB
        or sha256(encoded) != AUXILIARY_SHA256 or len(encoded) != 22995
        or raw.endswith("\n") or "\r" in raw or "\0" in raw
    ):
        raise ValueError("exact auxiliary source bytes and missing terminal LF are required")
    invalid = {path for path, content in raw_files.items() if not canonical_text(content)}
    if invalid != {AUXILIARY_CONTEXT_PATH}:
        raise ValueError("unexpected noncanonical source context: " + repr(sorted(invalid)))
    native_files = {path: content for path, content in raw_files.items() if path != AUXILIARY_CONTEXT_PATH}
    auxiliary = seal({
        "schema_version": "aoc-read-only-raw-source-v1",
        "role": "read_only_dependency_outside_native_patch_snapshot",
        "repository_full_name": pack["repository"],
        "baseline_commit_sha": pack["baseline_commit"],
        "path": AUXILIARY_CONTEXT_PATH,
        "original_git_blob_sha1": AUXILIARY_GIT_BLOB,
        "original_source_sha256": AUXILIARY_SHA256,
        "original_byte_count": len(encoded),
        "original_has_terminal_lf": False,
        "raw_source_utf8": raw,
        "source_normalization_performed": False,
        "editable_in_native_patch_snapshot": False,
    }, AUXILIARY_DIGEST_FIELD)
    projection = seal({
        "schema_version": "aoc-exact-source-transport-v1",
        "repository_full_name": pack["repository"],
        "baseline_commit_sha": pack["baseline_commit"],
        "baseline_tree_sha1": pack["baseline_tree"],
        "raw_observed_paths": sorted(raw_files),
        "raw_source_snapshot_digest": canonical_digest(raw_files),
        "native_observed_paths": sorted(native_files),
        "native_repository_snapshot_digest": canonical_digest(native_files),
        "auxiliary_path": AUXILIARY_CONTEXT_PATH,
        "auxiliary_source_digest": auxiliary[AUXILIARY_DIGEST_FIELD],
        "auxiliary_raw_source_sha256": AUXILIARY_SHA256,
        "excluded_from_native_repository_reason": "missing_terminal_lf",
        "auxiliary_transport": "sealed_json_in_synthesis_request_intent_text",
        "source_normalization_performed": False,
        "repository_source_mutation_performed": False,
    }, PROJECTION_DIGEST_FIELD)
    return native_files, auxiliary, projection


def intent_with_auxiliary_source(intent: str, auxiliary: dict) -> str:
    """Carry original source as data, without claiming another repository path."""
    return intent + "\n\nREAD_ONLY_ORIGINAL_SOURCE_ATTACHMENT_JSON\n" + json.dumps(
        auxiliary, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    )


def verify_native_prompt_context(prompt: dict, native_files: dict, intent_text: str) -> None:
    from runtime.kuuos_codeai_candidate_patch_envelope_v0_1 import canonical_digest
    if prompt.get("repository_files") != native_files or prompt.get("repository_snapshot_digest") != canonical_digest(native_files):
        raise ValueError("provider prompt does not match native source snapshot")
    if prompt.get("intent_text") != intent_text:
        raise ValueError("provider prompt auxiliary source transport differs")



def validate_candidate_contracts(pack: dict) -> None:
    """Preserve public definitions and theorem contracts across strategies."""
    if pack.get("unresolved_binding_slots"):
        raise ValueError("candidate pack has unresolved binding slots")
    declarations = pack.get("declarations")
    if not isinstance(declarations, list) or not declarations or any(
        not isinstance(name, str) or not name.startswith("MGAP4D.MathlibAnalytic.")
        for name in declarations
    ):
        raise ValueError("complete public declaration audit list is required")
    strategies = pack.get("strategies")
    if not isinstance(strategies, dict) or set(strategies) != {"A", "B"} or any(
        not isinstance(source, str) or not source for source in strategies.values()
    ):
        raise ValueError("two complete authored candidate strategies are required")
    namespace = "MGAP4D.MathlibAnalytic."
    expected_statements = None
    expected_preamble = None
    expected_imports = None
    for label, source in pack["strategies"].items():
        if FORBIDDEN.search(source) or not source.endswith("\n") or any(
            c in source for c in "\r\v\f\x1c\x1d\x1e\x85\u2028\u2029"
        ):
            raise ValueError("forbidden or incomplete candidate: " + label)
        statements = re.findall(r"(?ms)^theorem\s+(\w+)(.*?):=\s*by", source)
        public_names = re.findall(r"(?m)^(?:noncomputable )?(?:def|theorem)\s+(\w+)", source)
        imports = re.findall(r"(?m)^import .+$", source)
        if not statements or [namespace + name for name in public_names] != pack["declarations"]:
            raise ValueError("unexpected public declaration audit list")
        first_theorem = re.search(r"(?m)^theorem\s+", source)
        preamble = source[:first_theorem.start()]
        if expected_statements is None:
            expected_statements, expected_preamble, expected_imports = statements, preamble, imports
        else:
            if statements != expected_statements or imports != expected_imports:
                raise ValueError("candidates disagree on statements or imports")
            if preamble != expected_preamble:
                raise ValueError("candidates disagree on definition or preamble")


def synthesize(root: Path, pack: dict, output: Path):
    from runtime import kuuos_codeai_intent_repository_observation_envelope_v0_1 as obs
    from runtime import kuuos_codeai_candidate_patch_envelope_v0_1 as patch
    from runtime import kuuos_codeai_autonomous_structured_edit_synthesis_v0_1 as synth
    from runtime.kuuos_codeai_autonomous_unified_diff_candidates_v0_1 import render_unified_diff

    now = int(time.time())
    files = snapshot(root, pack)
    validate_candidate_contracts(pack)
    native_files, auxiliary, projection = prepare_native_context(files, pack)
    toolchain_digest = obs.canonical_digest({"lean": files["lean-toolchain"],
                                            "manifest": files["lake-manifest.json"]})
    intent = obs.seal({
        "intent_id": "PZ37AOC-local-center-flip-taylor", "source_actor_id": "itakura-hidetoshi",
        "source_channel": "ChatGPT user continuation 2026-11-22", "intent_revision": "r1",
        "requirements": ["Bound the original signed first-mode Haar Taylor remainder by 8 times the original action budget times beta squared using the native center flip"],
        "assumptions": ["H is an arbitrary finite original volume", "beta is any nonnegative real coupling", "the original one-link action oscillation is at most eight", "All seven original context blobs are verified; the native patch snapshot contains six canonical files and the unchanged LocalHarnack source is attached as sealed read-only JSON in request intent"],
        "unresolved_questions": [],
        "preserved_invariants": ["original physical Wilson/Haar/Hilbert definitions", "fixed Lean/mathlib"],
        "forbidden_changes": ["weaken theorem statements", "replace model", "introduce trust bypass"],
        "success_criteria": ["direct Lean", "real Lean MCP", "separate exact-source CI and axiom audit"],
        "authority_owner_id": "itakura-hidetoshi", "intent_created_epoch": now,
        "prior_intent_digests": [], "intent_provenance_confirmed": True,
    }, obs.INTENT_DIGEST_FIELD)
    observation = {key: False for key in obs.REPOSITORY_OBSERVATION_FIELDS}
    observation.update({
        "repository_full_name": pack["repository"], "source_commit_sha": pack["baseline_commit"],
        "source_branch": pack["baseline_branch"], "tree_digest": pack["baseline_tree"],
        "dependency_lock_digest": sha256(files["lake-manifest.json"]),
        "toolchain_digest": toolchain_digest, "toolchain_supported": True,
        "observed_paths": sorted(native_files), "unavailable_paths": [], "declared_path_count": len(native_files),
        "baseline_check_digests": [obs.canonical_digest(pack["baseline_ci"]), projection[PROJECTION_DIGEST_FIELD]],
        "baseline_checks_complete": True,
        "code_owner_scope_digest": obs.canonical_digest({"repository": pack["repository"],
                                                       "allowed_new_path": pack["target"]}),
        "observation_started_epoch": now, "observation_completed_epoch": now,
        "session_id": "aoc-" + uuid.uuid4().hex, "nonce_digest": sha256(uuid.uuid4().bytes),
        "prior_session_ids": [], "prior_nonce_digests": [], "prior_observation_digests": [],
    })
    observation = obs.seal(observation, obs.REPOSITORY_OBSERVATION_DIGEST_FIELD)
    observation_policy = obs.seal({
        "expected_repository_full_name": pack["repository"],
        "expected_source_commit_sha": pack["baseline_commit"],
        "allowed_source_branches": [pack["baseline_branch"]],
        "supported_toolchain_digests": [toolchain_digest], "maximum_observed_paths": 8,
        "maximum_observation_duration": 60, "require_complete_baseline": True,
        "require_code_owner_scope": True, "allow_partial_observation": False,
    }, obs.POLICY_DIGEST_FIELD)
    source = obs.build_codeai_intent_repository_observation_envelope(
        intent_packet=intent, repository_observation=observation,
        observation_policy=observation_policy)
    if source.status != "ready" or not source.receipt or source.receipt["codeai_disposition"] != "intent_repository_observation_supported":
        raise ValueError("source observation blocked: " + repr(asdict(source)))
    patch_policy = patch.seal({
        "expected_source_observation_receipt_digest": source.receipt[patch.SOURCE_RECEIPT_DIGEST_FIELD],
        "expected_repository_full_name": pack["repository"],
        "expected_source_commit_sha": pack["baseline_commit"],
        "allowed_patch_formats": ["unified_diff"], "maximum_patch_bytes": 40000,
        "maximum_changed_paths": 1, "allowed_path_prefixes": [pack["target"]],
        "forbidden_path_prefixes": [], "allow_deletions": False, "allow_renames": False,
        "allow_binary_patches": False, "allow_submodule_patches": False, "allow_mode_changes": False,
        "require_requirement_trace": True, "require_test_plan": True,
        "allow_evidence_degradation": False, "known_risk_labels": ["formal_proof"],
        "handover_risk_labels": [], "evaluation_epoch": now, "maximum_candidate_age": 3600,
    }, patch.POLICY_DIGEST_FIELD)
    request = synth.seal({
        "request_id": "AOC-local-center-flip-taylor-strategies", "request_revision": "r1",
        "intent_text": intent_with_auxiliary_source("Add original-model local center-flip Taylor estimates for the signed first Haar response at every nonnegative beta. Preserve the supplied theorem statements and original Haar/Wilson objects. No continuum mass-gap conclusion.", auxiliary),
        "candidate_count": 3, "request_created_epoch": now,
        "requirement_trace_ids": ["ANV:native-Haar-center-flip", "LocalHarnack:one-link-action-oscillation-eight", "AOC:signed-first-mode-Taylor-bound"],
        "test_plan_ids": ["direct-pinned-Lean", "real-Lean-MCP", "independent-exact-source-CI"],
        "risk_labels": ["formal_proof"], "unresolved_candidate_questions": [],
        "prior_candidate_digests": [], "prior_producer_session_ids": [],
    }, synth.REQUEST_DIGEST_FIELD)
    policy = synth.seal({
        "allowed_provider_ids": ["authored_strategy"], "maximum_provider_calls": 3,
        "maximum_raw_output_bytes": 40000, "maximum_intent_bytes": 40000,
        "maximum_repository_snapshot_bytes": 118369, "maximum_proposals": 3,
        "evaluation_epoch": now, "maximum_response_age": 3600, "maximum_request_age": 3600,
        "allowed_repository_path_prefixes": sorted(native_files),
        "forbidden_repository_path_prefixes": [],
    }, synth.POLICY_DIGEST_FIELD)
    proposals = {}

    def adapter(label, claims=False):
        def generate(prompt):
            verify_native_prompt_context(prompt, native_files, request["intent_text"])
            for source_path, required_names in pack["source_requirements"].items():
                if source_path not in files or any(
                    name not in files[source_path]
                    for name in required_names
                ):
                    raise ValueError("original source premise absent: " + source_path)
            proof = pack["strategies"]["A" if claims else label]
            proposal = {
                "proposal_id": "AOC-" + label, "candidate_revision": "r1",
                "edits": [{"path": pack["target"], "operation": "add", "new_content": proof}],
                "risk_labels": ["formal_proof"], "unresolved_candidate_questions": [],
            }
            proposals[proposal["proposal_id"]] = proposal
            return {
                "provider_response_id": "aoc-response-" + label,
                "producer_session_id": observation["session_id"] + "-" + label,
                "response_created_epoch": now, "raw_output": json.dumps(proposal, ensure_ascii=False),
                "claims_authority": claims, "hides_uncertainty": False,
                "bypasses_governance": False, "evidence_missing": False,
            }
        return synth.ProviderAdapter("aoc-" + label, "authored_strategy",
                                     "source-bound-authored-" + label, generate)

    result = synth.build_codeai_autonomous_structured_edit_synthesis(
        source_observation_receipt=source.receipt, repository_files=native_files,
        synthesis_request=request, provider_adapters=[adapter("A"), adapter("B"), adapter("C", True)],
        synthesis_policy=policy, candidate_policy=patch_policy)
    write_json(output / "synthesis.json", asdict(result))
    write_json(output / "source-observation.json", {
        "intent": intent, "observation": observation, "policy": observation_policy,
        "result": asdict(source), "baseline_ci": pack["baseline_ci"],
        "source_transport": projection, "auxiliary_source_attachment": auxiliary,
        "synthesis_request_digest": request[synth.REQUEST_DIGEST_FIELD]})
    if result.status != "ready" or len(result.candidates) != 2:
        raise ValueError("CodeAI synthesis blocked: " + repr(result.issues))
    if [a.boundary_status for a in result.attempts] != ["CANDIDATE", "CANDIDATE", "REJECT"]:
        raise ValueError("provider boundary audit differs")
    if result.receipt["candidate_selected"] or result.receipt["execution_authority_granted"]:
        raise ValueError("CodeAI authority boundary differs")
    emitted = []
    for candidate in result.candidates:
        proposal = proposals[candidate.proposal_id]
        rendered, accounting, issues = render_unified_diff(native_files, proposal["edits"])
        if issues or rendered != candidate.patch_artifact or accounting["added_paths"] != [pack["target"]]:
            raise ValueError("generated diff/source mismatch")
        text = proposal["edits"][0]["new_content"]
        lines = candidate.patch_artifact.splitlines()
        hunks = [i for i, line in enumerate(lines) if line.startswith("@@ ")]
        if len(hunks) != 1 or any(not line.startswith("+") for line in lines[hunks[0] + 1:]):
            raise ValueError("generated addition is not a complete single-file source")
        reconstructed = "\n".join(line[1:] for line in lines[hunks[0] + 1:]) + "\n"
        if reconstructed.encode() != text.encode():
            raise ValueError("emitted patch does not reconstruct the exact tested source bytes")
        (output / (candidate.proposal_id + ".lean")).write_text(text)
        emitted.append((candidate, text))
    return emitted, files


def verify_candidate(root: Path, output: Path, candidate, source: str, declarations: list[str]) -> dict:
    from scripts.check_kuuos_lean_lsp_mcp_compatibility_v7_17 import MCPClient, PROTOCOL_VERSION, call_tool, tool_map
    from scripts.check_kuuos_lean_mcp_parent_pr3522_v155_v1 import structured
    from scripts.kuuos_lean_mcp_repair_loop_v1 import require_semantics, DISABLED_MCP_TOOLS

    rel = Path("codeai_candidates") / "PZ37AOC" / candidate.proposal_id / "Candidate.lean"
    path = root / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(source)
    digest = sha256(source)
    require_exact_source(path, digest)
    command = ["lake", "env", "lean", "-DwarningAsError=true", "-o",
               str(output / (candidate.proposal_id + ".olean")), str(rel)]
    compiled = run_captured(command, root, 300)
    full_log = compiled["stdout"] + compiled["stderr"]
    (output / (candidate.proposal_id + "-direct.log")).write_text(full_log)
    record = {"proposal_id": candidate.proposal_id, "candidate_source_sha256": digest,
              "direct_lean": {"exit_code": compiled["exit_code"], "complete": compiled["complete"],
                              "candidate_source_sha256": digest,
                              "log_sha256": sha256(full_log), "command": command},
              "lean_mcp": None, "status": "DIRECT_FAILED"}
    try:
        record["direct_lean"]["audit"] = audit_lean_output(full_log, compiled["exit_code"], declarations)
    except ValueError as exc:
        record["obstruction"] = str(exc)
        print(full_log, flush=True)
        return record
    require_exact_source(path, digest)
    client = None
    try:
        client = MCPClient(
            ["uvx", "--from", "lean-lsp-mcp==0.30.0", "lean-lsp-mcp", "--transport", "stdio"],
            cwd=root, env={"LEAN_PROJECT_PATH": str(root), "LEAN_LOG_LEVEL": "NONE",
                          "LEAN_MCP_DISABLED_TOOLS": DISABLED_MCP_TOOLS, "LEAN_MCP_SCRATCH_SLOTS": "1"},
            timeout_seconds=240)
        initialization = client.request("initialize", {"protocolVersion": PROTOCOL_VERSION,
            "capabilities": {}, "clientInfo": {"name": "pz37aoc-codeai-validation", "version": "1"}})
        client.notify("notifications/initialized")
        available = tool_map(client.request("tools/list"))
        if "lean_diagnostic_messages" not in available or "lean_run_code" in available or "lean_build" in available:
            raise ValueError("Lean MCP tool boundary differs")
        raw = call_tool(client, "lean_diagnostic_messages", {"file_path": str(rel), "timeout_s": 120})
        write_json(output / (candidate.proposal_id + "-mcp.json"),
                   {"initialize": initialization, "diagnostics": raw})
        body = structured(raw)
        observation = require_semantics(body, require_exact_source(path, digest))
        record["lean_mcp"] = dict(body, candidate_source_sha256=digest)
        if not observation.success or any(d["severity"] in ("error", "warning") for d in observation.diagnostics):
            raise ValueError("Lean MCP is not complete and clean")
        record["status"] = "DIRECT_AND_REAL_MCP_SUCCESS_CANDIDATE_ONLY"
    except Exception as exc:
        record["status"] = "MCP_OBSTRUCTION"
        record["obstruction"] = type(exc).__name__ + ": " + str(exc)
    finally:
        if client is not None:
            client.close()
        require_exact_source(path, digest)
    return record


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--project-root", default=".")
    parser.add_argument("--candidate-pack", default="scripts/pz37aoc_candidate_strategies.json")
    parser.add_argument("--output-dir", required=True)
    parser.add_argument("--synthesize-only", action="store_true")
    parser.add_argument("--verify-source-tree", action="store_true")
    args = parser.parse_args()
    root, output = Path(args.project_root).resolve(), Path(args.output_dir).resolve()
    output.mkdir(parents=True, exist_ok=True)
    pin = Path(os.environ["KUUOS_CODEAI_PINNED_ROOT"]).resolve()
    sys.path.insert(0, str(pin))
    pack = json.loads(Path(args.candidate_pack).read_text())
    if args.verify_source_tree or not args.synthesize_only:
        original_count = verify_original_lean_tree(root, pack["baseline_mgap4d_tree"], pack["target"])
        if original_count != pack["baseline_mgap4d_file_count"]:
            raise ValueError("baseline MGAP4D source count changed")
        print(json.dumps({"baseline_source_tree_verified": pack["baseline_mgap4d_tree"],
                          "original_source_files": original_count}), flush=True)
    emitted, files = synthesize(root, pack, output)
    _, _, source_transport = prepare_native_context(files, pack)
    adopted_path = root / pack["target"]
    adopted_digest = sha256(adopted_path.read_bytes()) if adopted_path.is_file() else None
    if adopted_digest is not None and adopted_digest not in {sha256(source) for _, source in emitted}:
        raise ValueError("adopted source is not one of the emitted CodeAI candidate byte strings")
    print(json.dumps({"codeai_pin": KUUOS_PIN, "generated_candidates": len(emitted),
                      "live_model_inference": False, "mode": "authored-strategy-synthesis"}), flush=True)
    if args.synthesize_only:
        return 0
    records = []
    from pz37aoc_codeai_learning_handoff import build_aoc_learning_handoff
    for candidate, source in emitted:
        record = verify_candidate(root, output, candidate, source, pack["declarations"])
        records.append(record)
        learning = build_aoc_learning_handoff(
            source_binding={"repository_full_name": pack["repository"],
                            "source_commit_sha": pack["baseline_commit"],
                            "source_tree_sha": pack["baseline_tree"],
                            "source_actor_id": os.getenv("GITHUB_ACTOR"), "runner_id": os.getenv("RUNNER_NAME")},
            candidate_patch=candidate.patch_candidate, candidate_source=source, context_files=files,
            direct_lean_receipt=record["direct_lean"], lean_mcp_receipt=record["lean_mcp"],
            toolchain_receipt={"lean": files["lean-toolchain"].strip(),
                              "mathlib": "5450b53e5ddc75d46418fabb605edbf36bd0beb6"},
            environment_receipt={"run_id": os.getenv("GITHUB_RUN_ID"), "source_head": os.getenv("AOC_HEAD"),
                                 "runner_os": os.getenv("RUNNER_OS")},
            observed_epoch=int(time.time()), source_transport=source_transport)
        write_json(output / (candidate.proposal_id + "-learning-handoff.json"), learning)
        print(json.dumps({"proposal_id": candidate.proposal_id, "status": record["status"],
                          "source_sha256": record["candidate_source_sha256"],
                          "memory_promotion": learning["disposition"],
                          "ensemble_status": learning["native_ensemble"]["result"]["status"],
                          "memory_status": learning["native_subtask_memory"]["result"]["status"]}), flush=True)
        write_json(output / "validation.json", {"source_head": os.getenv("AOC_HEAD"),
                   "baseline_commit": pack["baseline_commit"], "codeai_pin": KUUOS_PIN,
                   "adopted_source_sha256": adopted_digest,
                   "candidates": records, "independent_ci_success": False,
                   "candidate_selected": False, "memory_promotion": "HOLD"})
    successful = {r["candidate_source_sha256"] for r in records
                  if r["status"] == "DIRECT_AND_REAL_MCP_SUCCESS_CANDIDATE_ONLY"}
    return 0 if successful and (adopted_digest is None or adopted_digest in successful) else 1


if __name__ == "__main__":
    raise SystemExit(main())
