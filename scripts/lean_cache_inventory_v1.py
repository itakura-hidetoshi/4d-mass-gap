#!/usr/bin/env python3
"""Measure cache contents; this does not establish a safe dependency closure."""
from collections import defaultdict
import json
from pathlib import Path
import stat
import sys

def inventory(root):
    groups = defaultdict(lambda: {"files": 0, "logical_bytes": 0, "allocated_bytes": 0})
    for path in root.rglob("*"):
        if path.is_symlink():
            continue
        s = path.stat()
        if not stat.S_ISREG(s.st_mode):
            continue
        kind = path.suffix or "(no extension)"
        row = groups[kind]
        row["files"] += 1
        row["logical_bytes"] += s.st_size
        row["allocated_bytes"] += getattr(s, "st_blocks", 0) * 512
    return dict(sorted(groups.items(), key=lambda kv: -kv[1]["logical_bytes"]))

result = {
    "mode": "inventory_only_no_cache_pruning",
    "roots": {name: inventory(Path(path)) for name, path in (
        ("mathlib_and_packages", ".lake/packages"),
        ("project_build", ".lake/build"),
    )},
    "closure_verified": False,
}
Path(sys.argv[1]).write_text(json.dumps(result, indent=2) + "\n")
print("WARM_CACHE_INVENTORY " + json.dumps(result), flush=True)
