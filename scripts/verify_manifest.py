#!/usr/bin/env python3
"""Verify MGAP4D release manifest metadata.

This script checks that FILE_MANIFEST.json records the expected v1.6 package
hash and top-level package contents. It intentionally avoids depending on the
large Zenodo zip being present in the GitHub repository.
"""

from __future__ import annotations

import json
from pathlib import Path
import sys

EXPECTED_PACKAGE = "MGAP4D_v1_6_Zenodo_release_package.zip"
EXPECTED_SHA256 = "afc2c81f3f9b20a2bf92e93fb9417ab53f0a7e46a6769eb68be8d14407c69ab0"
EXPECTED_TOP_LEVEL = {
    "MGAP4D_v1_6_final_review_packet_with_hash_manifest.zip",
    "MGAP4D_v1_6_expanded_source_snapshot.zip",
    "zenodo_metadata.json",
    "CITATION.cff",
    "LICENSE",
    "README_ZENODO.md",
    "RELEASE_SUMMARY.md",
    "ZENODO_UPLOAD_CHECKLIST.md",
    "FILE_MANIFEST.json",
}


def fail(message: str) -> None:
    print(f"ERROR: {message}", file=sys.stderr)
    raise SystemExit(1)


def main() -> None:
    manifest_path = Path("FILE_MANIFEST.json")
    if not manifest_path.exists():
        fail("FILE_MANIFEST.json not found")

    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))

    if manifest.get("package") != EXPECTED_PACKAGE:
        fail(f"unexpected package: {manifest.get('package')!r}")

    if manifest.get("package_sha256") != EXPECTED_SHA256:
        fail("package_sha256 mismatch")

    top_level = set(manifest.get("top_level_files", []))
    missing = sorted(EXPECTED_TOP_LEVEL - top_level)
    extra = sorted(top_level - EXPECTED_TOP_LEVEL)

    if missing:
        fail(f"missing top-level entries: {missing}")
    if extra:
        fail(f"unexpected top-level entries: {extra}")

    audit = manifest.get("audit_summary", {})
    expected_audit = {
        "lean_files": 12308,
        "declarations": 52137,
        "sorry": 0,
        "admit": 0,
        "axiom": 0,
        "constant": 0,
    }
    for key, expected in expected_audit.items():
        actual = audit.get(key)
        if actual != expected:
            fail(f"audit_summary.{key} expected {expected}, got {actual}")

    print("manifest verification passed")


if __name__ == "__main__":
    main()
