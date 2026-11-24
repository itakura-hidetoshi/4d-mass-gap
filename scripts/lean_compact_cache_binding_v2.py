#!/usr/bin/env python3
"""Exact canonical provenance for the additive compact-cache publisher.

No repository writes or paid inference. Only the trusted push workflow uses
the API-reading prepare command. Consumers must still verify actual Lean.
"""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
import urllib.parse
import urllib.request

from pz37aoi_codeai_candidate_pipeline import snapshot, verify_original_lean_tree

PROFILE = "warm-project-nosetup-v2"
FORMAL_REF = "refs/heads/formal/real-hilbert-uniform-coercive-strong-limit"
FORMAL_BRANCH = FORMAL_REF.removeprefix("refs/heads/")
PIN_PATHS = ("lean-toolchain", "lakefile.lean", "lake-manifest.json")
RECEIPT = Path(".lake/build/warm-nosetup-v2-receipt.json")
SHA = re.compile(r"[0-9a-f]{40}")

def require(ok, message):
    if not ok:
        raise ValueError(message)

def exact_sha(value):
    require(isinstance(value, str) and SHA.fullmatch(value) is not None, "invalid exact SHA")
    return value

def source_binding(tree):
    require(not tree.get("truncated"), "truncated root tree")
    by_path = {r["path"]: r for r in tree["tree"]}
    math = by_path["MGAP4D"]
    require(math["type"] == "tree", "MGAP4D is not a source tree")
    pins = {}
    for path in PIN_PATHS:
        item = by_path[path]
        require(item["type"] == "blob", "pin not a blob")
        pins[path] = exact_sha(item["sha"])
    return {"baseline_mgap4d_tree": exact_sha(math["sha"]), "baseline_blobs": pins}

def select_cache_base(current, current_binding, bootstrap, bootstrap_binding):
    exact_sha(current)
    exact_sha(bootstrap)
    return bootstrap if current_binding == bootstrap_binding else current

def successful_push(run, jobs, base):
    if (run.get("head_sha") != base or run.get("event") != "push" or
            run.get("head_branch") != FORMAL_BRANCH or
            run.get("status") != "completed" or run.get("conclusion") != "success"):
        return False
    lean = [j for j in jobs if j.get("name") == "Changed Lean fast check"]
    receipt = [j for j in jobs if j.get("name") == "Publish MCP CI completion receipt"]
    if len(lean) != 1 or len(receipt) != 1:
        return False
    for job in (lean[0], receipt[0]):
        if job.get("status") != "completed" or job.get("conclusion") != "success":
            return False
    steps = [s for s in lean[0].get("steps", []) if s.get("name") == "Run changed Lean fast check"]
    save = [s for s in lean[0].get("steps", []) if s.get("name") == "Save MGAP4D project olean cache from trusted branches"]
    return (len(steps) == 1 and steps[0].get("status") == "completed" and
            steps[0].get("conclusion") == "success" and len(save) == 1 and
            save[0].get("status") == "completed" and save[0].get("conclusion") in {"success", "skipped"})

def verify_binding(root, pack):
    exact_sha(pack["baseline_commit"])
    snapshot(root, pack)
    return verify_original_lean_tree(root, pack["baseline_mgap4d_tree"], "__never_allow__")

def api(path):
    root = os.environ["GITHUB_API_URL"].rstrip("/")
    repo = os.environ["GITHUB_REPOSITORY"]
    require(repo == "itakura-hidetoshi/4d-mass-gap", "wrong repository")
    req = urllib.request.Request(root + "/repos/" + repo + path, headers={
        "Accept": "application/vnd.github+json",
        "Authorization": "Bearer " + os.environ["GH_TOKEN"],
        "X-GitHub-Api-Version": "2022-11-28",
    })
    with urllib.request.urlopen(req, timeout=30) as response:
        return json.load(response)

def binding_for(commit):
    c = api("/git/commits/" + exact_sha(commit))
    require(c["sha"] == commit, "commit identity mismatch")
    return source_binding(api("/git/trees/" + exact_sha(c["tree"]["sha"])))

def prepare(args):
    require(os.environ.get("GITHUB_EVENT_NAME") == "push" and
            os.environ.get("GITHUB_REF") == FORMAL_REF, "publisher requires trusted Formal push")
    head = exact_sha(os.environ["GITHUB_SHA"])
    bootstrap = exact_sha(args.bootstrap)
    current = binding_for(head)
    old = binding_for(bootstrap)
    base = select_cache_base(head, current, bootstrap, old)
    pack = {"baseline_commit": base, **current}
    verify_binding(Path.cwd().resolve(), pack)
    # An infrastructure-only push may reuse the exact bootstrap mathematical
    # tree, but no unrelated proof tree or pin is accepted.
    deadline = time.monotonic() + 720
    run = None
    while time.monotonic() < deadline:
        query = urllib.parse.urlencode({"head_sha": base, "event": "push", "per_page": 20})
        runs = api("/actions/workflows/pr-lean-fast-check.yml/runs?" + query)["workflow_runs"]
        matches = [r for r in runs if r.get("head_sha") == base and r.get("event") == "push"
                   and r.get("head_branch") == FORMAL_BRANCH]
        if matches:
            run = max(matches, key=lambda r: (r["id"], r["run_attempt"]))
            if run.get("status") == "completed":
                jobs = api(f"/actions/runs/{run['id']}/attempts/{run['run_attempt']}/jobs?per_page=100")["jobs"]
                require(successful_push(run, jobs, base), "exact trusted Lean push did not pass")
                break
        print("COMPACT_WAIT exact trusted Lean push " + base, flush=True)
        time.sleep(15)
    else:
        raise ValueError("HOLD: exact trusted Lean push not completed")
    commit = api("/commits/" + base + "?per_page=100")
    require(commit.get("sha") == base, "changed-file commit mismatch")
    files = commit.get("files", [])
    require(0 < len(files) < 100, "HOLD: changed files absent or require pagination")
    modules = []
    for item in files:
        name = item["filename"]
        if name.startswith("MGAP4D/") and name.endswith(".lean") and item["status"] != "removed":
            module = name[:-5].replace("/", ".")
            require(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.]*", module), "unsupported module path")
            modules.append(module)
    require(modules, "HOLD: selected baseline has no changed Lean modules")
    data = {**pack, "profile": PROFILE, "publisher_head": head, "proof_run_id": run["id"],
            "proof_run_attempt": run["run_attempt"], "proof_job_id": next(
                j["id"] for j in jobs if j["name"] == "Changed Lean fast check"),
            "proof_status": "completed_success", "imports": sorted(set(modules))}
    Path(args.output).parent.mkdir(parents=True, exist_ok=True)
    Path(args.output).write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
    with open(os.environ["GITHUB_OUTPUT"], "a") as out:
        out.write("base=" + base + "\n")
    print("COMPACT_BINDING " + json.dumps(data, sort_keys=True), flush=True)

def seal(args):
    data = json.loads(Path(args.binding).read_text())
    verify_binding(Path.cwd().resolve(), data)
    require(data["proof_status"] == "completed_success" and data["profile"] == PROFILE,
            "invalid proof lineage")
    require(not any(Path(".lake/build/ir").rglob("*.setup.json")), "setup JSON remains")
    subprocess.run(["lake", "build", "--no-build", *data["imports"]], check=True, timeout=300)
    require(not any(Path(".lake/build/ir").rglob("*.setup.json")), "setup JSON regenerated")
    require(not RECEIPT.exists(), "unexpected existing receipt")
    data["cache_validation"] = "exact_no_build_imports_success"
    RECEIPT.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
    print("COMPACT_SEALED " + json.dumps(data, sort_keys=True), flush=True)

def check_receipt(args):
    pack = json.loads(Path(args.pack).read_text())
    data = json.loads(RECEIPT.read_text())
    require(data["profile"] == PROFILE and data["proof_status"] == "completed_success" and
            data["cache_validation"] == "exact_no_build_imports_success", "invalid compact receipt")
    for k in ("baseline_commit", "baseline_mgap4d_tree", "baseline_blobs"):
        require(data[k] == pack[k], "compact receipt differs: " + k)
    require(type(data["proof_run_id"]) is int and data["proof_run_id"] > 0, "proof run missing")
    require(not any(Path(".lake/build/ir").rglob("*.setup.json")), "compact cache contains setup JSON")
    verify_binding(Path.cwd().resolve(), pack)
    print("COMPACT_RECEIPT_MATCH " + json.dumps(data, sort_keys=True), flush=True)

def main():
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("prepare")
    p.add_argument("--bootstrap", required=True)
    p.add_argument("--output", required=True)
    p = sub.add_parser("seal")
    p.add_argument("--binding", required=True)
    p = sub.add_parser("check-receipt")
    p.add_argument("--pack", required=True)
    args = parser.parse_args()
    {"prepare": prepare, "seal": seal, "check-receipt": check_receipt}[args.command](args)

if __name__ == "__main__":
    main()
