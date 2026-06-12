# Independent Replay Guide

This document gives a minimal independent replay procedure for the MGAP4D Lean 4 repository.

## Scope

This guide checks the public repository state only. It confirms the repository audit chain, physical Hamiltonian scalar/operator normalization surfaces, complete infinite-dimensional Hilbert construction lane, downstream lane hardening chain, four-lane residual closure, internal review residual closure gate, external audit readiness gate, OS/Wightman--Euclidean construction route, replay summary, Lake manifest generation, and Lean build.

It does not claim external mathematical consensus, peer-review completion, Clay-style public final theorem acceptance, an unconditional construction of the Euclidean Yang--Mills measure, external acceptance of the OS/Wightman bridge, external acceptance of the construction-spine external-audit projection, or a dimensional physical mass gap without an external reference scale `E0`.

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

This executes the full replay path. The OS/Wightman--Euclidean route includes:

```text
[check] audit OS/Wightman mass-gap bridge
[check] build OS/Wightman mass-gap external audit bridge
[check] build Euclidean Yang-Mills measure to mass-gap pipeline
[check] build unconditional Euclidean Yang-Mills measure target
[check] build Euclidean Yang-Mills measure construction spine
[check] build Euclidean Yang-Mills construction external audit bridge
[check] lake build
```

## Manual replay

```bash
python3 scripts/verify_manifest.py
python3 scripts/audit_lean_forbidden_tokens.py
python3 scripts/audit_major_theorem_nonplaceholder.py
python3 scripts/audit_proof_placeholder_inventory.py
python3 scripts/audit_bridge_coherence.py
python3 scripts/audit_final_physical_carrier_routing.py
python3 scripts/audit_external_audit_readiness_gate.py
python3 scripts/audit_external_audit_readiness_gate_field_classification.py
python3 scripts/audit_external_audit_readiness_replay_certificate.py
python3 scripts/audit_os_wightman_mass_gap_bridge.py
python3 scripts/replay_summary.py
lake update
lake build MGAP4D.MathlibAnalytic.ExternalAuditReadinessGate
lake build MGAP4D.MathlibAnalytic.OSWightmanMassGapExternalAuditBridge
lake build MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureToMassGapPipeline
lake build MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureUnconditionalTarget
lake build MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureConstructionSpine
lake build MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureConstructionExternalAuditBridge
lake build
```

## OS/Wightman--Euclidean construction replay route

```text
AxiomaticYangMillsMassGapClosure
  -> OSWightmanHamiltonianReconstructionSpine
  -> OSWightmanMassGapDefinitionBridge
  -> OSWightmanMassGapExternalAuditBridge
  -> EuclideanYangMillsMeasureToMassGapPipeline
  -> EuclideanYangMillsMeasureUnconditionalTarget
  -> EuclideanYangMillsMeasureConstructionSpine
  -> EuclideanYangMillsMeasureConstructionExternalAuditBridge
```

The construction-facing theorem route is:

```text
EuclideanYangMillsFiniteVolumeApproximation
  -> EuclideanYangMillsContinuumMeasureConstructionSpine
  -> EuclideanYangMillsMeasureUnconditionalConstructionTarget
  -> EuclideanYangMillsMeasureMassGapPipeline
  -> OSWightmanMassGapDefinitionBridge
  -> ExternalAuditReadinessOSWightmanMassGapDefinitionBridgeProjection
  -> ExternalAuditReadinessEuclideanYangMillsConstructionSpineProjection
```

Primary anchors:

```text
euclidean_yang_mills_continuum_spine_limit_ready
euclidean_yang_mills_continuum_spine_os_axioms_ready
euclidean_yang_mills_continuum_spine_wightman_theory
euclidean_yang_mills_continuum_spine_positive_hamiltonian_spectrum
euclidean_yang_mills_continuum_spine_vacuum_isolated
euclidean_yang_mills_continuum_spine_first_excitation_pvm_detected
euclidean_yang_mills_continuum_spine_mass_gap_definition
euclidean_yang_mills_finite_volume_continuum_construction_mass_gap
external_audit_readiness_euclidean_yang_mills_construction_spine_projection
external_audit_readiness_euclidean_construction_spine_exact_gap_positive
external_audit_readiness_euclidean_construction_spine_exact_gap_threshold
external_audit_readiness_euclidean_construction_spine_pvm_detects_first_excitation
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
Older confirmed CI checkpoints in this repository predate the current OS/Wightman--Euclidean construction external-audit bridge additions.
A reviewer should record a fresh Full Local Check CI run against the reviewed commit.
```

## Review boundary

A successful independent replay means the repository builds with the pinned Lean toolchain, declared audit scripts pass, physical Hamiltonian operator normalization is present and audited, lane-hardening and closure gates pass, the external audit readiness gate passes, the OS/Wightman--Euclidean construction route builds through `EuclideanYangMillsMeasureConstructionExternalAuditBridge`, and the replay summary is reproducible.

It does not mean external consensus has been obtained, that the gate layers alone complete the physical continuum proof, that the Euclidean Yang--Mills measure has been externally accepted, or that the construction-spine external-audit projection is itself external acceptance.
