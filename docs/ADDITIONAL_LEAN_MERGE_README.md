# Additional Lean Merge Manifest

The v1.6 expanded source snapshot integrates prior MGAP4D Lean project archives using an append-only strategy.

## Policy

- The active v1.6 `MGAP4D/` root is not silently overwritten.
- Prior Lean project ZIP contents are preserved under archive locations in the source snapshot.
- Lean-only extracts are treated as additional proof-kernel material.
- Merge metadata records SHA256 values and file counts.

## Integration principle

The archive is a lineage-preserving source snapshot. The GitHub mirror should migrate it in batches:

1. active R1--R7 skeleton;
2. root manifests and maps;
3. prior-project archive indexes;
4. selected prior Lean kernels;
5. final hash and review manifests.

## Active root

```text
MGAP4D.lean
MGAP4D/
  R1/Basic.lean
  R2/Basic.lean
  R3/Basic.lean
  R4/Basic.lean
  R5/Basic.lean
  R6/Basic.lean
  R7/Basic.lean
  Global/FinalAssembly.lean
  Map.lean
```

## Review rule

Archived prior kernels should not be imported into the active root until each batch passes:

```bash
python3 scripts/verify_manifest.py
python3 scripts/audit_lean_forbidden_tokens.py
lake update
lake build
```

## Public gate

The archive records internal proof-kernel lineage. Public finality remains review-gated and independent-replay-gated.
