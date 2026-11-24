#!/usr/bin/env python3
"""One restored runner, bounded exact-source candidates, one lazy Lean MCP client.
No git writes, no canonical or memory promotion, no live paid inference.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import time

from pz37aoi_codeai_candidate_pipeline import (
    audit_lean_output, audit_complete_mcp_output, require_exact_source,
    run_captured, snapshot, verify_original_lean_tree, write_json,
)

GREEN = "DIRECT_AND_REAL_MCP_SUCCESS_CANDIDATE_ONLY"
PIN = "3c3d4a9127256fff732749fdfddd3118b30e86ab"

def digest(raw):
    return hashlib.sha256(raw).hexdigest()

def blob(raw):
    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()

def check(ok, message):
    if not ok:
        raise ValueError(message)

def ident(value):
    check(isinstance(value, str) and re.fullmatch(r"[A-Za-z0-9_]+", value), "invalid candidate identifier")
    return value

def source_contract(source):
    return (
        re.findall(r"(?m)^import .+$", source),
        re.findall(r"(?ms)^theorem\s+(\w+)(.*?):=\s*by", source),
        re.findall(r"(?m)^#print axioms (\S+)\s*$", source),
    )

def read_candidate(root, candidate, declarations, imports):
    path = (root / candidate["path"]).resolve()
    check(path.is_relative_to(root / "diagnostics"), "candidate source escapes diagnostics")
    raw = path.read_bytes()
    check(blob(raw) == candidate["blob"], "candidate git blob mismatch")
    source = raw.decode("utf-8")
    check(source.endswith("\n"), "source must end in newline")
    check(not re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b|debug\.skipKernelTC", source),
          "forbidden proof construct")
    check(not re.search(r"(?m)^\s*set_option\s+(?:linter\.|warningAsError|autoImplicit)", source),
          "candidate must not override strict gates")
    actual_imports, _, names = source_contract(source)
    check(actual_imports == ["import " + item for item in imports], "unexpected imports")
    check(names == declarations and len(set(names)) == len(names), "axiom audit list mismatch")
    return raw

def validate_pack(root, pack):
    check(pack["schema"] == 1 and pack["codeai_pin"] == PIN, "unsupported pack or CodeAI pin")
    snapshot(root, pack)
    count = verify_original_lean_tree(root, pack["baseline_mgap4d_tree"], "__never_allow__")
    groups = {}
    check(0 < len(pack["groups"]) <= 8, "group limit")
    for group in pack["groups"]:
        gid = ident(group["id"])
        check(gid not in groups and 0 < len(group["candidates"]) <= 8, "duplicate group or candidate limit")
        check(bool(group["declarations"]), "empty declaration audit")
        seen = set()
        entries = []
        contract = None
        for candidate in group["candidates"]:
            cid = ident(candidate["id"])
            check(cid not in seen, "duplicate candidate")
            seen.add(cid)
            raw = read_candidate(root, candidate, group["declarations"], pack["imports"])
            current = source_contract(raw.decode())
            check(contract is None or current == contract, "public statements/imports changed")
            contract = current
            entries.append((candidate, raw))
        groups[gid] = (group, entries)
    return count, groups

class WarmMCP:
    def __init__(self, root):
        self.root = root
        self.client = None
        self.starts = 0
        self.calls = 0

    def verify(self, path, raw, declarations, direct, out):
        from scripts.check_kuuos_lean_lsp_mcp_compatibility_v7_17 import (
            MCPClient, PROTOCOL_VERSION, call_tool, tool_map,
        )
        from scripts.check_kuuos_lean_mcp_parent_pr3522_v155_v1 import structured
        from scripts.kuuos_lean_mcp_repair_loop_v1 import DISABLED_MCP_TOOLS, require_semantics
        if self.client is None:
            self.client = MCPClient(
                ["uvx", "--from", "lean-lsp-mcp==0.30.0", "lean-lsp-mcp", "--transport", "stdio"],
                cwd=self.root,
                env={"LEAN_PROJECT_PATH": str(self.root), "LEAN_LOG_LEVEL": "NONE",
                     "LEAN_MCP_DISABLED_TOOLS": DISABLED_MCP_TOOLS, "LEAN_MCP_SCRATCH_SLOTS": "1"},
                timeout_seconds=240,
            )
            self.starts += 1
            self.client.request("initialize", {"protocolVersion": PROTOCOL_VERSION,
                "capabilities": {}, "clientInfo": {"name": "warm-exact-lean-audit", "version": "1"}})
            self.client.notify("notifications/initialized")
            tools = tool_map(self.client.request("tools/list"))
            check("lean_diagnostic_messages" in tools and "lean_build" not in tools and
                  "lean_run_code" not in tools, "Lean MCP tool boundary differs")
        require_exact_source(path, digest(raw))
        self.calls += 1
        result = call_tool(self.client, "lean_diagnostic_messages",
                           {"file_path": str(path.relative_to(self.root)), "timeout_s": 120})
        write_json(out / "mcp-raw.json", result)
        body = structured(result)
        observation = require_semantics(body, raw)
        check(observation.success and not observation.partial and not observation.errors,
              "MCP incomplete or errors")
        receipt = audit_complete_mcp_output(body, declarations, direct)
        require_exact_source(path, digest(raw))
        return receipt

    def close(self):
        if self.client is not None:
            self.client.close()

def evaluate(root, output, pack, groups, client, compile_candidate=run_captured):
    records = []
    winners = {}
    start = time.monotonic()
    for gid, (group, entries) in groups.items():
        previous = None
        for candidate, raw in entries:
            cid = candidate["id"]
            out = output / gid / cid
            out.mkdir(parents=True, exist_ok=False)
            path = root / "codeai_candidates" / "WarmV1" / gid / cid / "Candidate.lean"
            path.parent.mkdir(parents=True, exist_ok=False)
            if "repair" in candidate:
                from scripts.kuuos_lean_mcp_repair_loop_v1 import patch_source
                rule = candidate["repair"]
                check(previous is not None and previous[0]["status"] == "DIRECT_FAILED" and
                      previous[0]["complete"] and rule["requires_log"] in previous[2],
                      "repair not justified by prior terminal direct diagnostic")
                patch = {k: rule[k] for k in ("old_text", "new_text", "reason")}
                patch["expected_sha256"] = digest(previous[1])
                generated = patch_source(previous[1].decode(), patch).encode()
                check(generated == raw, "native repaired bytes differ from exact candidate blob")
                write_json(out / "repair.json", {"patch": patch, "result_sha256": digest(raw)})
            path.write_bytes(raw)
            (out / "Candidate.lean").write_bytes(raw)
            t = time.monotonic()
            result = compile_candidate(
                ["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                 "-o", str(out / "Candidate.olean"), str(path.relative_to(root))], root, 420,
            )
            log = result["stdout"] + result["stderr"]
            (out / "direct.log").write_text(log)
            record = {"group": gid, "candidate": cid, "blob": blob(raw), "sha256": digest(raw),
                      "source_head": os.environ.get("EXACT_HEAD"), "baseline_commit": pack["baseline_commit"],
                      "direct_seconds": round(time.monotonic() - t, 3), "complete": result["complete"],
                      "exit_code": result["exit_code"], "mcp_seconds": 0, "mcp_called": False,
                      "status": "DIRECT_FAILED", "independent_ci_success": False,
                      "source_promoted": False, "memory_promoted": False}
            require_exact_source(path, digest(raw))
            try:
                check(result["complete"], "direct Lean incomplete")
                direct = audit_lean_output(log, result["exit_code"], group["declarations"])
                record["direct_audit"] = direct
            except ValueError as exc:
                record["obstruction"] = str(exc)
                print(log[-10000:], flush=True)
            else:
                t = time.monotonic()
                record["mcp_called"] = True
                try:
                    record["mcp_audit"] = client.verify(path, raw, group["declarations"], direct, out)
                    record["status"] = GREEN
                except Exception as exc:
                    record["status"] = "MCP_OBSTRUCTION"
                    record["obstruction"] = str(exc)
                record["mcp_seconds"] = round(time.monotonic() - t, 3)
            require_exact_source(path, digest(raw))
            write_json(out / "receipt.json", record)
            records.append(record)
            print(json.dumps(record, sort_keys=True), flush=True)
            previous = (record, raw, log)
            if candidate.get("expected"):
                expected = GREEN if candidate["expected"] == "GREEN" else candidate["expected"]
                check(record["status"] == expected, "benchmark outcome differs")
            if record["status"] == GREEN:
                winners[gid] = record["sha256"]
                break
            if record["status"] == "MCP_OBSTRUCTION":
                break
    receipt = {"baseline_commit": pack["baseline_commit"], "head": os.environ.get("EXACT_HEAD"),
               "records": records, "winners": winners, "mcp_client_starts": client.starts,
               "mcp_calls": client.calls, "elapsed_candidate_seconds": round(time.monotonic() - start, 3),
               "independent_ci_success": False, "source_promoted": False, "memory_promoted": False}
    return receipt

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--pack", required=True)
    parser.add_argument("--output", required=True)
    parser.add_argument("--preflight", action="store_true")
    args = parser.parse_args()
    root = Path.cwd().resolve()
    pack = json.loads(Path(args.pack).read_text())
    count, groups = validate_pack(root, pack)
    if args.preflight:
        print(json.dumps({"preflight": "PASS", "baseline_files": count, "groups": list(groups)}), flush=True)
        return 0
    output = Path(args.output).resolve()
    output.mkdir(parents=True, exist_ok=True)
    sys.path.insert(0, str(root / "_codeai_pinned"))
    client = WarmMCP(root)
    try:
        receipt = evaluate(root, output, pack, groups, client)
        check(verify_original_lean_tree(root, pack["baseline_mgap4d_tree"], "__never_allow__") == count,
              "baseline source tree changed")
        receipt["baseline_tree_preserved"] = True
        write_json(output / "summary.json", receipt)
        print("WARM_SANDBOX_SUMMARY " + json.dumps(receipt, sort_keys=True), flush=True)
        return 0 if set(receipt["winners"]) == set(groups) else 1
    finally:
        client.close()

if __name__ == "__main__":
    raise SystemExit(main())
