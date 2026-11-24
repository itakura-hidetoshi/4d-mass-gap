#!/usr/bin/env python3
"""Isolate only regenerable Lake setup input files on a disposable runner.
No shared cache is mutated or saved. Keep originals in a quarantine directory.
"""
import json
import os
from pathlib import Path
import stat
import sys
import time

root = Path(".lake/build").resolve()
ir = root / "ir"
assert ir.is_dir()
quarantine = Path(".lake/warm-nosetup-quarantine-v1").resolve()
assert not quarantine.exists() and not quarantine.is_relative_to(root)
quarantine.mkdir()
start = time.monotonic()
files = []
for path in sorted(ir.rglob("*.setup.json")):
    st = path.lstat()
    if not stat.S_ISREG(st.st_mode):
        raise ValueError("Unexpected nonregular setup file: " + str(path))
    rel = path.relative_to(root)
    dest = quarantine / rel
    dest.parent.mkdir(parents=True, exist_ok=True)
    os.replace(path, dest)
    files.append({"path": str(rel), "bytes": st.st_size})
if not files:
    raise ValueError("No setup.json files found: HOLD, not a compact-cache result")
report = {
    "mode": "quarantine_setup_json_only",
    "files": len(files), "logical_bytes": sum(f["bytes"] for f in files),
    "sample": files[:8], "full_remote_cache_untouched": True,
    "quarantine_seconds": round(time.monotonic() - start, 3),
    "lean_validation": "pending",
}
out = Path(sys.argv[1])
out.parent.mkdir(parents=True, exist_ok=True)
out.write_text(json.dumps({"summary": report, "files": files}, indent=2) + "\n")
print("WARM_NOSETUP_QUARANTINE " + json.dumps(report, sort_keys=True), flush=True)
