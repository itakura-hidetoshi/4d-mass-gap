# Archived Release Integrity Notes

This document records historical package-integrity metadata from the MGAP4D v1.6 release package.

The active GitHub project is organized as a Lean 4 repository. Active development status is tracked by:

```text
README.md
ROADMAP.md
.github/workflows/lean-direct-elan.yml
MGAP4D.lean
```

## Historical package hash

```text
MGAP4D_v1_6_Zenodo_release_package.zip
SHA256 afc2c81f3f9b20a2bf92e93fb9417ab53f0a7e46a6769eb68be8d14407c69ab0
```

## Historical package contents

```text
MGAP4D_v1_6_final_review_packet_with_hash_manifest.zip
MGAP4D_v1_6_expanded_source_snapshot.zip
zenodo_metadata.json
CITATION.cff
LICENSE
README_ZENODO.md
RELEASE_SUMMARY.md
ZENODO_UPLOAD_CHECKLIST.md
FILE_MANIFEST.json
```

## GitHub-native rule

The repository root should remain focused on active Lean development. Release metadata is retained under archive/provenance documentation and should not determine the active source layout.

## Tagging rule

Do not create a final release tag until:

1. active source migration is complete;
2. `lake build` passes on GitHub Actions;
3. audit scripts pass;
4. source maps are reviewed;
5. independent replay has been completed or the tag is explicitly marked as a development checkpoint.
