# External audit readiness replay certificate

This document records a compact replay certificate for the current external-audit-readiness checkpoint.

It is intended to help an independent reviewer locate the repository-internal evidence chain without interpreting CI success as external mathematical consensus.

This file is documentation-only. It does not modify Lean semantics. It does not open final theorem release. It does not claim independent external mathematical consensus.

## Checkpoint identity

```text
Repository: itakura-hidetoshi/4d-mass-gap
Checkpoint commit: de76fd42f0e5c3bfd58090bfb2eef2510f6b5d63
Workflow run: 25973699153
Workflow job: 76350067649
Job name: Run scripts/check.sh
Result: success
```

## Replay route

The reviewed checkpoint used the repository's standard replay command:

```bash
bash scripts/check.sh
```

The script route includes the following final Lean build targets:

```bash
lake build MGAP4D.MathlibAnalytic.ExternalAuditReadinessGate
lake build
```

The reviewed job reported:

```text
Build completed successfully (8368 jobs).
[check] lake build
Build completed successfully (0 jobs).
```

## Lean audit summary at checkpoint

```text
Lean files scanned: 457
sorry: 0
admit: 0
axiom: 0
constant: 0
Major theorem specs audited: 12
Bridge files audited: 8
```

The replay summary emitted by the script route reported:

```text
lean_files: 457
imports: 1191
declaration_like_lines: 2663
namespace_lines: 938
total_lines: 27611
```

## Final gate surfaces reached by the replay

The checkpoint reached these final surfaces under the standard check route:

```text
MGAP4D.MathlibAnalytic.ExactGapReal
MGAP4D.MathlibAnalytic.ExactGapAnalyticRealClosure
MGAP4D.MathlibAnalytic.ExactGapFullInterfaceClosure
MGAP4D.MathlibAnalytic.ExactGapTheoremBodyClosure
MGAP4D.MathlibAnalytic.ExactValueTheoremBodyOrigin
MGAP4D.MathlibAnalytic.InfiniteDimensionalResidualFillingBridge
MGAP4D.MathlibAnalytic.HardPhysicalResidualHardeningMap
MGAP4D.MathlibAnalytic.HilbertConstructionLaneHardening
MGAP4D.MathlibAnalytic.SelfAdjointHPhysLaneHardening
MGAP4D.MathlibAnalytic.ContinuumYangMillsLaneHardening
MGAP4D.MathlibAnalytic.PlaquetteSpectralWeightLaneHardening
MGAP4D.MathlibAnalytic.FourLaneResidualClosure
MGAP4D.MathlibAnalytic.InternalReviewResidualClosureGate
MGAP4D.MathlibAnalytic.ExternalAuditReadinessGate
```

## Named readiness theorem route

The final gate is exposed through named Lean theorem witnesses including:

```text
external_audit_readiness_internal_gate_ready_witness
external_audit_readiness_bundle_manifest_ready_witness
external_audit_readiness_chain_index_ready_witness
external_audit_readiness_repository_internal_residual_closed_witness
external_audit_readiness_no_review_level_residual_left_witness
external_audit_readiness_independent_replay_visible_witness
external_audit_readiness_audit_script_route_visible_witness
external_audit_readiness_ci_route_visible_witness
external_audit_readiness_external_audit_ready_witness
external_audit_readiness_external_consensus_not_claimed_witness
external_audit_readiness_public_boundary_held_witness
external_audit_readiness_final_release_held_witness
external_audit_readiness_exact_value_preserved_witness
external_audit_readiness_gate_ready
```

## Exact value preservation route

The exact normalized value remains exposed as:

```text
exactGapValueReal = (33 : ℝ) / 20
```

and is carried into the external-audit-readiness gate through:

```text
external_audit_readiness_exact_value_preserved_witness
external_audit_readiness_exact_value_preserved
```

## Boundary interpretation

This certificate means:

```text
repository-internal Lean replay succeeded
repository-internal audit scripts passed
external-audit-readiness gate built successfully
forbidden Lean tokens were absent in the scanned Lean files
exact normalized value surface was preserved through the gate
```

This certificate does not mean:

```text
external audit completed
external mathematical consensus obtained
final theorem release opened
future residuals impossible
public theorem boundary removed
```

## Reviewer checklist

A reviewer can independently replay the current route by checking:

```text
1. lean --version reports Lean 4.30.0-rc2 or a declared compatible toolchain.
2. lake --version reports the matching Lake version.
3. bash scripts/check.sh completes.
4. lake build MGAP4D.MathlibAnalytic.ExternalAuditReadinessGate completes.
5. lake build completes.
6. scripts/audit_lean_forbidden_tokens.py reports sorry/admit/axiom/constant all zero.
7. scripts/audit_external_audit_readiness_gate.py passes.
8. scripts/audit_external_audit_readiness_gate_field_classification.py passes.
```

## Status

```text
Status: replay-certificate prepared
Semantic effect: documentation-only
Lean semantics changed: no
External consensus claimed: no
External audit completed: no
Final theorem release opened: no
```