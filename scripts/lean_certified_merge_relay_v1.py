#!/usr/bin/env python3
"""Exact independent-PR leaf artifact relay; a cache is not proof authority."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import stat
import subprocess
import urllib.error
import urllib.parse
import urllib.request
import zipfile

REPO = "itakura-hidetoshi/4d-mass-gap"
FORMAL = "formal/real-hilbert-uniform-coercive-strong-limit"
WORKFLOW = ".github/workflows/pr-lean-fast-check.yml"
PIN_PATHS = ("lean-toolchain", "lakefile.lean", "lake-manifest.json")
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
BUILD = Path(".lake/build")
LEAF = re.compile(r"MGAP4D/MathlibAnalytic/[A-Za-z_][A-Za-z0-9_]*[.]lean")
MAX_BYTES = 512 * 1024 * 1024
MAX_FILES = 1024

def require(ok, msg):
    if not ok:
        raise ValueError(msg)

def sha(value):
    require(isinstance(value, str) and re.fullmatch(r"[0-9a-f]{40}", value), "invalid SHA")
    return value

def git(*args):
    return subprocess.check_output(["git", *args], text=True).strip()

def binding(ref):
    return {"tree": sha(git("rev-parse", ref + "^{tree}")),
            "math_tree": sha(git("rev-parse", ref + ":MGAP4D")),
            "pins": {p: sha(git("rev-parse", ref + ":" + p)) for p in PIN_PATHS}}

def leaf_modules(diff):
    rows = [line.split("\t") for line in diff.splitlines() if line]
    require(0 < len(rows) <= 32, "not a bounded leaf-only addition")
    require(all(len(row) == 2 and row[0] == "A" and LEAF.fullmatch(row[1])
                for row in rows), "non-leaf change or modification")
    paths = sorted(row[1] for row in rows)
    require(len(paths) == len(set(paths)), "duplicate leaf")
    return paths

def parent_pair(ref):
    row = git("rev-list", "--parents", "-n", "1", ref).split()
    require(len(row) == 3 and row[0] == ref, "not an exact two-parent merge")
    return sha(row[1]), sha(row[2])

def event():
    return json.loads(Path(os.environ["GITHUB_EVENT_PATH"]).read_text())

def output(key, value):
    with open(os.environ["GITHUB_OUTPUT"], "a") as out:
        out.write(f"{key}={value}\n")

def write_json(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")

def file_digest(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()

def safe_artifact_path(value, leaves):
    require(isinstance(value, str) and "\\" not in value, "bad artifact path")
    p = PurePosixPath(value)
    require(not p.is_absolute() and ".." not in p.parts and str(p) == value,
            "noncanonical artifact path")
    allowed = any(p.parent == PurePosixPath(root + "/" + leaf).parent and
                  p.name.startswith(PurePosixPath(leaf).stem + ".")
                  for leaf in leaves for root in ("lib/lean", "ir"))
    require(allowed and len(p.name) < 240, "artifact not an added leaf output")
    return p

def audit_requests(leaves):
    names = [n for leaf in leaves for n in
             re.findall(r"(?m)^#print axioms (\S+)\s*$", Path(leaf).read_text())]
    require(names and len(names) == len(set(names)), "missing or duplicate audit requests")
    return names

def audited_declarations(leaves, log):
    clean = re.sub(r"\x1b\[[0-9;]*m", "", log)
    require(re.search(r"Build completed successfully \([0-9]+ jobs\)", clean),
            "no completed Lake build evidence")
    for leaf in leaves:
        require(re.search(r"(?m)^#print axioms \S+", Path(leaf).read_text()), "leaf lacks audit")
        require(not re.search(r"(?:warning|error):\s*" + re.escape(leaf) + r":|"
                              + re.escape(leaf) + r":[^\n]*:\s*(?:warning|error):", clean),
                "leaf warning or error")
    out = {}
    for name in audit_requests(leaves):
        matches = re.findall(r"'" + re.escape(name) + r"' depends on axioms: \[([^\]]*)\]", clean)
        empty = re.findall(r"'" + re.escape(name) + r"' does not depend on any axioms", clean)
        require(len(matches) + len(empty) == 1, "missing/ambiguous audit " + name)
        axioms = sorted(x.strip() for x in matches[0].split(",") if x.strip()) if matches else []
        require(set(axioms) <= ALLOWED, "forbidden axiom " + name)
        out[name] = axioms
    return out

def collect_delta(leaves, build, out):
    records = []
    total = 0
    for leaf in leaves:
        stem = leaf[:-5]
        require((build / ("lib/lean/" + stem + ".olean")).is_file(), "new olean missing")
        for root in ("lib/lean", "ir"):
            prefix = build / root / stem
            for p in sorted(prefix.parent.glob(prefix.name + ".*")):
                require(p.is_file() and not p.is_symlink() and
                        p.resolve().is_relative_to(build.resolve()), "nonregular leaf output")
                rel = p.relative_to(build).as_posix()
                safe_artifact_path(rel, leaves)
                size = p.stat().st_size
                total += size
                require(total <= MAX_BYTES and len(records) < MAX_FILES, "leaf delta too large")
                dest = out / "delta" / rel
                dest.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(p, dest)
                records.append({"path": rel, "size": size, "sha256": file_digest(dest)})
    require(records, "no leaf outputs")
    return sorted(records, key=lambda r: r["path"])

def produce(args):
    ev = event()["pull_request"]
    require(os.environ["GITHUB_EVENT_NAME"] == "pull_request" and
            ev["head"]["repo"]["full_name"] == REPO and ev["base"]["ref"] == FORMAL,
            "not same-repository Formal PR")
    merge = sha(git("rev-parse", "HEAD"))
    base, head = parent_pair(merge)
    require(base == ev["base"]["sha"] and head == ev["head"]["sha"], "test merge parents differ")
    leaves = leaf_modules(git("diff", "--name-status", "--no-renames", base, merge))
    b = binding(merge)
    require(b == binding(head) and b["pins"] == binding(base)["pins"], "source tree or pins changed")
    out = Path(args.output)
    out.mkdir(parents=True, exist_ok=False)
    audit = audited_declarations(leaves, Path(args.log).read_text())
    rec = {"schema": 1, "repository": REPO, "pr": ev["number"],
           "run_id": int(os.environ["GITHUB_RUN_ID"]), "attempt": int(os.environ["GITHUB_RUN_ATTEMPT"]),
           "base": base, "head": head, "test_merge": merge, "binding": b,
           "leaves": leaves, "audit": audit, "files": collect_delta(leaves, BUILD, out)}
    write_json(out / "receipt.json", rec)
    print("CERTIFIED_LEAF_DELTA " + json.dumps({k:v for k,v in rec.items() if k != "files"}, sort_keys=True))
    output("eligible", "true")

def api(path):
    require(os.environ["GITHUB_REPOSITORY"] == REPO, "wrong repository")
    req = urllib.request.Request(os.environ["GITHUB_API_URL"].rstrip("/") + "/repos/" + REPO + path,
        headers={"Accept": "application/vnd.github+json", "Authorization": "Bearer " + os.environ["GH_TOKEN"],
                 "X-GitHub-Api-Version": "2022-11-28"})
    with urllib.request.urlopen(req, timeout=30) as r:
        return json.load(r)

def completed_success(x):
    return x.get("status") == "completed" and x.get("conclusion") == "success"

def step_success(job, name):
    steps = [s for s in job.get("steps", []) if s.get("name") == name]
    return len(steps) == 1 and completed_success(steps[0])

def proof_job(run, jobs, head, branch):
    require(run.get("event") == "pull_request" and run.get("head_sha") == head
            and run.get("head_branch") == branch and run.get("path") == WORKFLOW
            and run.get("head_repository", {}).get("full_name") == REPO
            and completed_success(run), "independent PR workflow not exact GREEN")
    lean = [j for j in jobs if j.get("name") == "Changed Lean fast check"]
    receipt = [j for j in jobs if j.get("name") == "Publish MCP CI completion receipt"]
    require(len(lean) == len(receipt) == 1 and completed_success(lean[0]) and
            completed_success(receipt[0]), "independent Lean job or receipt not GREEN")
    for name in ("Run changed Lean fast check", "Publish certified added-leaf delta"):
        require(step_success(lean[0], name), "step not GREEN: " + name)
    return lean[0]["id"]

def exact_artifact(run, artifacts, head):
    name = f'lean-certified-leaf-delta-v1-{run["id"]}-{run["run_attempt"]}'
    items = [a for a in artifacts if a.get("name") == name and not a.get("expired")]
    require(len(items) == 1, "exact leaf artifact missing or ambiguous")
    a = items[0]
    origin = a.get("workflow_run", {})
    require(origin.get("id") == run["id"] and origin.get("head_sha") == head and
            origin.get("repository_id") == origin.get("head_repository_id") == run["repository"]["id"],
            "artifact origin mismatch")
    require(re.fullmatch(r"sha256:[0-9a-f]{64}", a.get("digest") or ""), "artifact digest missing")
    require(0 < a["size_in_bytes"] <= MAX_BYTES + 8 * 1024 * 1024, "artifact size out of bounds")
    return a

class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None

def download_artifact(a, dest):
    # Do not forward the repository token to the signed archive URL.
    req = urllib.request.Request(os.environ["GITHUB_API_URL"].rstrip("/") + "/repos/" + REPO +
        f'/actions/artifacts/{int(a["id"])}/zip',
        headers={"Authorization": "Bearer " + os.environ["GH_TOKEN"],
                 "Accept": "application/vnd.github+json"})
    try:
        urllib.request.build_opener(NoRedirect()).open(req, timeout=30)
        raise ValueError("expected artifact redirect")
    except urllib.error.HTTPError as exc:
        require(exc.code in {301,302,303,307,308}, "artifact redirect unavailable")
        url = exc.headers["Location"]
    u = urllib.parse.urlsplit(url)
    require(u.scheme == "https" and u.hostname and not u.username and not u.password, "bad archive URL")
    count = 0
    with urllib.request.urlopen(url, timeout=120) as stream, dest.open("wb") as out:
        while chunk := stream.read(1024 * 1024):
            count += len(chunk)
            require(count <= MAX_BYTES + 8 * 1024 * 1024, "archive exceeds limit")
            out.write(chunk)
    require("sha256:" + file_digest(dest) == a["digest"], "archive digest mismatch")

def validate_receipt(rec, expected, test_tree, test_parents):
    for key in ("schema", "repository", "pr", "run_id", "attempt", "base", "head", "binding", "leaves"):
        require(rec.get(key) == expected[key], "receipt mismatch: " + key)
    sha(rec["test_merge"])
    require(test_tree == expected["binding"]["tree"] and
            test_parents == [expected["base"], expected["head"]], "independent test merge differs")
    require(isinstance(rec.get("audit"), dict) and rec["audit"] and
            all(isinstance(v, list) and set(v) <= ALLOWED for v in rec["audit"].values()),
            "invalid axiom audit")
    require(set(audit_requests(expected["leaves"])) == set(rec["audit"]), "audit coverage differs")

def extract_delta(archive, rec, dest):
    records = rec["files"]
    require(isinstance(records, list) and 0 < len(records) <= MAX_FILES, "bad file manifest")
    expected = {}
    total = 0
    for r in records:
        rel = str(safe_artifact_path(r["path"], rec["leaves"]))
        require(rel not in expected and isinstance(r["size"], int) and r["size"] >= 0 and
                re.fullmatch(r"[0-9a-f]{64}", r["sha256"]), "invalid file manifest")
        expected[rel] = r
        total += r["size"]
    require(total <= MAX_BYTES, "expanded delta too large")
    require(all("lib/lean/" + p[:-5] + ".olean" in expected for p in rec["leaves"]),
            "missing audited olean")
    with zipfile.ZipFile(archive) as z:
        files = [i for i in z.infolist() if not i.is_dir()]
        names = [i.filename for i in files]
        require(len(names) == len(set(names)) and set(names) ==
                {"receipt.json"} | {"delta/" + p for p in expected}, "unexpected artifact files")
        for i in files:
            require(not stat.S_ISLNK(i.external_attr >> 16), "symlink in archive")
            if i.filename == "receipt.json":
                continue
            rel = i.filename.removeprefix("delta/")
            r = expected[rel]
            require(i.file_size == r["size"], "archive file size mismatch")
            p = dest / rel
            p.parent.mkdir(parents=True, exist_ok=True)
            with z.open(i) as src, p.open("wb") as out:
                shutil.copyfileobj(src, out)
            require(file_digest(p) == r["sha256"], "leaf digest mismatch")

def exact_push_cache_job(run, jobs, base):
    if not (run.get("head_sha") == base and run.get("head_branch") == FORMAL and
            run.get("path") == WORKFLOW and run.get("event") == "push" and completed_success(run)):
        return False
    for j in jobs:
        if not completed_success(j):
            continue
        if j["name"] == "Changed Lean fast check" and step_success(j, "Run changed Lean fast check"):
            if step_success(j, "Save MGAP4D project olean cache from trusted branches"):
                return True
        if j["name"] == "Relay independently certified Lean leaf outputs" and step_success(j, "Publish exact merge reuse outcome"):
            if step_success(j, "Verify delta and no-build imports without re-elaboration") and step_success(j, "Publish exact merged full cache without a second Lean build"):
                return True
    return False

def require_base_provenance(base):
    runs = api("/actions/workflows/pr-lean-fast-check.yml/runs?" +
        urllib.parse.urlencode({"head_sha":base,"event":"push","per_page":20}))["workflow_runs"]
    runs = [r for r in runs if r.get("head_sha") == base and r.get("head_branch") == FORMAL]
    require(runs, "predecessor has no trusted cache publication run")
    run = max(runs, key=lambda r: (r["id"],r["run_attempt"]))
    jobs = api(f'/actions/runs/{run["id"]}/attempts/{run["run_attempt"]}/jobs?per_page=100')["jobs"]
    require(exact_push_cache_job(run,jobs,base), "predecessor cache provenance unavailable")

def prepare(args):
    require(os.environ["GITHUB_EVENT_NAME"] == "push" and
            os.environ["GITHUB_REF"] == "refs/heads/" + FORMAL, "not trusted Formal push")
    merged = sha(git("rev-parse", "HEAD"))
    base, head = parent_pair(merged)
    require(merged == os.environ["GITHUB_SHA"] and base == event()["before"], "push range not exact merge")
    leaves = leaf_modules(git("diff", "--name-status", "--no-renames", base, merged))
    b = binding(merged)
    require(b == binding(head) and b["pins"] == binding(base)["pins"], "source tree or pins differ")
    require_base_provenance(base)
    prs = [p for p in api("/commits/" + merged + "/pulls?per_page=100")
           if p.get("merge_commit_sha") == merged and p.get("merged_at") and
           p["base"]["ref"] == FORMAL and p["base"]["sha"] == base and
           p["head"]["sha"] == head and p["head"]["repo"]["full_name"] == REPO]
    require(len(prs) == 1, "exact merged PR association missing")
    pr = prs[0]
    runs = api("/actions/workflows/pr-lean-fast-check.yml/runs?" +
        urllib.parse.urlencode({"head_sha":head,"event":"pull_request","per_page":20}))["workflow_runs"]
    candidates = [r for r in runs if r.get("head_sha") == head and
                  r.get("head_branch") == pr["head"]["ref"] and r.get("path") == WORKFLOW]
    require(candidates, "no independent PR run")
    run = max(candidates, key=lambda r: (r["id"],r["run_attempt"]))
    jobs = api(f'/actions/runs/{run["id"]}/attempts/{run["run_attempt"]}/jobs?per_page=100')["jobs"]
    job_id = proof_job(run, jobs, head, pr["head"]["ref"])
    artifacts = api(f'/actions/runs/{run["id"]}/artifacts?per_page=100')["artifacts"]
    a = exact_artifact(run, artifacts, head)
    out = Path(args.output)
    out.mkdir(parents=True, exist_ok=False)
    archive = out / "bundle.zip"
    download_artifact(a, archive)
    with zipfile.ZipFile(archive) as z:
        require(z.getinfo("receipt.json").file_size <= 2 * 1024 * 1024, "receipt too large")
        rec = json.loads(z.read("receipt.json"))
    test = api("/git/commits/" + sha(rec["test_merge"]))
    require(test["sha"] == rec["test_merge"], "test merge identity mismatch")
    expected = {"schema":1,"repository":REPO,"pr":pr["number"],"run_id":run["id"],
                "attempt":run["run_attempt"],"base":base,"head":head,"binding":b,"leaves":leaves}
    validate_receipt(rec, expected, test["tree"]["sha"], [p["sha"] for p in test["parents"]])
    extract_delta(archive, rec, out / "verified-delta")
    rec.update({"merged_commit":merged,"independent_job_id":job_id,
                "artifact_id":a["id"],"artifact_digest":a["digest"]})
    write_json(out / "verified-receipt.json", rec)
    print("RELAY_PROVENANCE_MATCH " + json.dumps({k:v for k,v in rec.items() if k != "files"}, sort_keys=True))
    output("base", base)
    output("eligible", "true")

def apply_delta(args):
    out = Path(args.output)
    rec = json.loads((out / "verified-receipt.json").read_text())
    require(rec["merged_commit"] == git("rev-parse", "HEAD") and rec["binding"] == binding("HEAD"),
            "checkout changed after provenance validation")
    require(BUILD.is_dir() and not BUILD.is_symlink(), "exact baseline build unavailable")
    for r in rec["files"]:
        rel = str(safe_artifact_path(r["path"], rec["leaves"]))
        src = out / "verified-delta" / rel
        dst = BUILD / rel
        require(src.is_file() and not src.is_symlink() and file_digest(src) == r["sha256"],
                "staged leaf changed")
        require(not dst.exists() and not dst.is_symlink() and dst.resolve().is_relative_to(BUILD.resolve()),
                "refuse overwrite or escaping baseline")
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(src, dst)
    targets = [p[:-5].replace("/", ".") for p in rec["leaves"]]
    subprocess.run(["lake","build","--no-build",*targets], check=True, timeout=300)
    rec["cache_validation"] = "exact_no_build_imports_success"
    write_json(BUILD / "lean-certified-relay-v1-receipt.json", rec)
    write_json(out / "published-receipt.json", rec)
    print("RELAY_NO_BUILD_SUCCESS " + json.dumps({"merged_commit":rec["merged_commit"],
        "independent_run_id":rec["run_id"], "artifact_id":rec["artifact_id"], "targets":targets}, sort_keys=True))

def main():
    p = argparse.ArgumentParser()
    sub = p.add_subparsers(dest="cmd", required=True)
    for cmd in ("produce","prepare","apply"):
        s = sub.add_parser(cmd)
        s.add_argument("--output",required=True)
        if cmd == "produce":
            s.add_argument("--log",required=True)
    args = p.parse_args()
    # Only preflight/producer eligibility is optional. Failed overlay/import
    # never publishes a cache; the separate fallback job has a clean runner.
    if args.cmd == "apply":
        apply_delta(args)
    else:
        try:
            {"produce":produce,"prepare":prepare}[args.cmd](args)
        except Exception as exc:
            print("CERTIFIED_RELAY_HOLD: " + str(exc))
            output("eligible","false")

if __name__ == "__main__":
    main()
