# MGAP4D v1.6 Release Integrity

## Canonical package hash

```text
MGAP4D_v1_6_Zenodo_release_package.zip
SHA256 afc2c81f3f9b20a2bf92e93fb9417ab53f0a7e46a6769eb68be8d14407c69ab0
```

## Top-level release package contents

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

## GitHub mirror status

The repository currently mirrors the metadata and CI scaffold first. The expanded source snapshot should be migrated in smaller batches so that each batch can be checked by GitHub Actions.

## Final tagging rule

Do not create the final `v1.6` Git tag until all of the following are true:

1. the expanded source tree has been migrated;
2. `lake build` passes on GitHub Actions;
3. audit scripts pass;
4. hash manifest and file manifest are present;
5. release metadata agrees with Zenodo metadata.
