# Independent Replay Guide

This document gives a minimal independent replay procedure for the MGAP4D Lean 4 repository.

## Scope

This guide checks the public repository state only. It confirms the repository audit chain, physical Hamiltonian scalar/operator normalization surfaces, complete infinite-dimensional Hilbert construction lane, downstream lane hardening chain, four-lane residual closure, internal review residual closure gate, external audit readiness gate, replay summary, Lake manifest generation, and Lean build.

It does not claim external mathematical consensus, peer-review completion, Clay-style public final theorem acceptance, or a dimensional physical mass gap without an external reference scale `E0`.

## Fresh clone replay

```bash
git clone https://github.com/itakura-hidetoshi/4d-mass-gap.git
cd 4d-mass-gap
cat lean-toolchain
lean --version
lake --version
```

Expected Lean family:

```text
Lean 4.30.0-rc2
Lake 5.0.0-src+3dc1a08 or compatible Lake for the pinned Lean toolchain
```

## One-command repository check

```bash
bash scripts/check.sh
```

This executes, in order:

```text
[check] verify manifest
[check] audit Lean forbidden tokens
[check] audit major theorem non-placeholder surfaces
[check] audit analytic bridge coherence
[check] audit physical Hamiltonian operator normalization
[check] audit infinite-dimensional Yang-Mills target layer
[check] audit infinite-dimensional residual filling bridge
[check] audit hard physical residual hardening map
[check] audit complete infinite-dimensional Hilbert construction
[check] audit self-adjoint HPhys lane hardening
[check] audit continuum Yang-Mills lane hardening
[check] audit plaquette spectral weight lane hardening
[check] audit continuum Hamiltonian witness hardening
[check] audit four-lane residual closure
[check] audit internal review residual closure gate
[check] audit external audit readiness gate
[check] audit external audit readiness gate field classification
[check] audit external audit readiness replay certificate
[check] replay summary
[check] lake update
[check] build physical Hamiltonian operator normalization
[check] build continuum Hamiltonian exact mass-gap derivation
[check] build continuum Hamiltonian release-chain addendum
[check] build external audit readiness gate
[check] lake build
```

## Manual replay

```bash
python3 scripts/verify_manifest.py
python3 scripts/audit_lean_forbidden_tokens.py
python3 scripts/audit_major_theorem_nonplaceholder.py
python3 scripts/audit_bridge_coherence.py
python3 scripts/audit_physical_hamiltonian_operator_normalization.py
python3 scripts/audit_infinite_dimensional_target_layer.py
python3 scripts/audit_infinite_dimensional_residual_filling.py
python3 scripts/audit_hard_physical_residual_hardening_map.py
python3 scripts/audit_complete_infinite_dimensional_hilbert_construction.py
python3 scripts/audit_self_adjoint_hphys_lane_hardening.py
python3 scripts/audit_continuum_yang_mills_lane_hardening.py
python3 scripts/audit_plaquette_spectral_weight_lane_hardening.py
python3 scripts/audit_continuum_hamiltonian_mass_gap_witness_hardening.py
python3 scripts/audit_four_lane_residual_closure.py
python3 scripts/audit_internal_review_residual_closure_gate.py
python3 scripts/audit_external_audit_readiness_gate.py
python3 scripts/audit_external_audit_readiness_gate_field_classification.py
python3 scripts/audit_external_audit_readiness_replay_certificate.py
python3 scripts/replay_summary.py
lake update
lake build MGAP4D.MathlibAnalytic.PhysicalHamiltonianOperatorNormalization
lake build MGAP4D.MathlibAnalytic.ContinuumHamiltonianExactMassGapDerivation
lake build MGAP4D.MathlibAnalytic.FinalTheoremReleaseChainIndexContinuumHamiltonianAddendum
lake build MGAP4D.MathlibAnalytic.ExternalAuditReadinessGate
lake build
```

## Normalization replay boundary

The theorem-body value is dimensionless:

```text
exactGapValueReal = 33 / 20
Delta_norm = 33/20
```

The physical Hamiltonian operator normalization is:

```text
H_norm = E0^{-1} * H_phys
H_phys = E0 * H_norm
Delta_phys(E0) = E0 * (33/20)
```

In internal normalized units:

```text
E0 = 1
Delta_phys(1) = 33/20
```

A reviewer should not read `33/20` as a dimensional mass value unless an external reference scale `E0` has been chosen.

## Residual closure chain

```text
PhysicalHamiltonianNormalizationBridge
  -> PhysicalHamiltonianOperatorNormalization
  -> InfiniteDimensionalYangMillsRealizationTargets
  -> InfiniteDimensionalResidualFillingBridge
  -> HardPhysicalResidualHardeningMap
      -> CompleteInfiniteDimensionalHilbertConstruction
      -> HilbertToPhysicalUnboundedOperatorBridge
      -> SelfAdjointHPhysBridgeAdoption
      -> SelfAdjointHPhysLaneHardening
      -> ContinuumYangMillsLaneHardening
      -> PlaquetteSpectralWeightLaneHardening
  -> ContinuumHamiltonianMassGapWitness
  -> ContinuumHamiltonianExactMassGapDerivation
  -> ContinuumHamiltonianMassGapWitnessHardening
  -> ContinuumHamiltonianMassGapTheorem
  -> ContinuumHamiltonianMassGapReleaseAdoption
  -> ContinuumHamiltonianCompleteMassGapDerivation
  -> ContinuumHamiltonianCompleteMassGapReleaseAdoption
  -> FourLaneResidualClosure
  -> InternalReviewResidualClosureGate
  -> ExternalAuditReadinessGate
```

The former `HilbertConstructionLaneHardening` route has been superseded as the active Hilbert lane by `CompleteInfiniteDimensionalHilbertConstruction`.

## External audit readiness anchors

```text
repositoryInternalResidualClosed
noReviewLevelResidualLeft
independentReplayVisible
auditScriptRouteVisible
ciRouteVisible
externalAuditReady
externalConsensusNotClaimed
publicBoundaryHeld
finalReleaseHeld
exactValuePreserved
```

## GitHub Actions parity

The main replay path is mirrored by:

```text
.github/workflows/full-local-check.yml
```

The external audit readiness gate also has a dedicated workflow:

```text
.github/workflows/external-audit-readiness-ci.yml
```

## Latest checkpoint

```text
Pull request: #47
Head commit: a41f44cda3bf1f98b454d40f5364b3731ce39243
Merge commit: b65e6d596831f244edb31234dd5c847e32aa8419
Bridge Coherence CI: success
Lean Direct Elan CI: success
Full Local Check CI: success
External Audit Readiness CI: success
Observed timestamp: 2026-05-17
```

## Operator-normalization checkpoint

```text
Pull request: #46
Head commit: a212a163fe98067dee2a3704022d1e9271172554
Merge commit: 62ce858efb9006c458a4370c3bac23d7a137db69
Workflow: Full Local Check CI
Workflow run ID: 25992161524
Result: success
Observed timestamp: 2026-05-17
```

## Review boundary

A successful independent replay means the repository builds with the pinned Lean toolchain, declared audit scripts pass, physical Hamiltonian operator normalization is present and audited, lane-hardening and closure gates pass, the external audit readiness gate passes, and the replay summary is reproducible.

It does not mean external consensus has been obtained or that the gate layers alone complete the physical continuum proof.
