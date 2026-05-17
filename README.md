# MGAP4D

MGAP4D is a Lean 4 repository for developing, checking, and auditing the proof architecture of a normalized 4D mass gap theorem.

The repository is GitHub-native: Lean source, CI, audit scripts, replay guides, theorem-surface maps, bridge audits, target-obligation layers, physical-Hamiltonian normalization surfaces, continuum-Hamiltonian release surfaces, and public-boundary ledgers live directly in this repository.

## Repository role

This repository is the canonical Lean proof repository for the MGAP4D normalized 4D mass gap proof architecture.

```text
Canonical proof repo: itakura-hidetoshi/4d-mass-gap
KuuOS reference repo: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
```

KuuOS reference documents do not replace this repository as the canonical Lean proof repository and do not independently open final public theorem release.

## Current theorem claim and boundary

Inside the MGAP4D Lean proof architecture, the current theorem-body surface records the normalized exact spectral gap value:

```text
exactGapValueReal = 33 / 20
```

The repository treats `33/20` as an internal normalized theorem-body value, not as a packaging artifact, CI artifact, manifest-only artifact, or prototype-only release wrapper.

The physical Hamiltonian normalization is now recorded at both scalar-gap and operator-scale levels:

```text
H_norm = E0^{-1} * H_phys
H_phys = E0 * H_norm
normalizedGap = physicalGap / E0
physicalGap = E0 * normalizedGap
Delta_norm = 33/20
Delta_phys(E0) = E0 * (33/20)
```

In MGAP4D internal normalized units:

```text
E0 = 1
normalizedGap = exactGapValueReal = 33/20
Delta_phys(1) = 33/20
```

Thus `33/20` is the dimensionless spectral gap of the normalized physical Hamiltonian. A dimensional physical gap requires an external reference scale `E0`.

The repository currently records an internal normalized proof-architecture theorem surface with CI, bridge-audit, target-obligation, residual-hardening, operator-level Hamiltonian normalization, continuum-Hamiltonian theorem/release-adoption, complete-derivation, complete-release-adoption, and external-audit-readiness support.

It does **not** claim:

```text
external mathematical consensus
independent peer-review completion
Clay-style public final theorem acceptance
a dimensional physical mass gap without choosing E0
that CI ledgers replace mathematical proof review
that bridge-coherence audit replaces Lean kernel checking
that the external-audit-readiness gate replaces independent replay
```

The public final theorem boundary remains review-gated pending independent replay and external audit.

## Active Lean roots and dependency lane

```text
MGAP4D.lean
MGAP4D/MathlibAnalytic.lean
```

The current Lake project pins Lean/mathlib through:

```text
leanprover/lean4:v4.30.0-rc2
mathlib4 @ v4.30.0-rc2
```

The `MathlibAnalytic` root is a scoped analytic lane. It does not by itself open public final theorem release.

## Main analytic hardening chain

```text
Exact normalized value / real positivity
  -> gap infimum / Rayleigh lower bound / Rayleigh attainment
  -> spectral mass / exact gap analytic closure
  -> Hilbert, H_phys, spectral theorem, PVM, observable interfaces
  -> theorem-body surfaces for Hilbert, H_phys, spectral theorem, PVM, observable atom
  -> compact plaquette and operator-measure compatibility
  -> exact gap theorem-body closure
  -> concrete Hilbert and H_phys realization
  -> infinite-dimensional Hilbert necessity and excitation-family support
  -> Hilbert countable basis / density / topology / completion / inner-product / instance skeletons
  -> physical unbounded-operator and concrete Yang-Mills Hamiltonian skeletons
  -> spectral realization and continuum spectral theorem skeletons
  -> final theorem release skeleton / closure / chain index / bundle manifest
  -> concrete residual closure
  -> physical Hamiltonian normalization bridge
  -> physical Hamiltonian operator normalization
  -> infinite-dimensional Yang-Mills realization targets
  -> infinite-dimensional residual filling bridge
  -> hard physical residual hardening map
  -> complete infinite-dimensional Hilbert construction
  -> Hilbert-to-physical unbounded-operator bridge
  -> self-adjoint H_phys bridge adoption
  -> self-adjoint H_phys lane hardening
  -> continuum Yang-Mills lane hardening
  -> plaquette spectral weight lane hardening
  -> continuum Hamiltonian mass-gap witness hardening
  -> continuum Hamiltonian mass-gap theorem
  -> continuum Hamiltonian mass-gap release adoption
  -> continuum Hamiltonian complete mass-gap derivation
  -> continuum Hamiltonian complete mass-gap release adoption
  -> four-lane residual closure
  -> internal review residual closure gate
  -> external audit readiness gate
```

Representative source files:

```text
MGAP4D/MathlibAnalytic/ExactGapReal.lean
MGAP4D/MathlibAnalytic/ExactGapTheoremBodyClosure.lean
MGAP4D/MathlibAnalytic/ConcreteResidualClosure.lean
MGAP4D/MathlibAnalytic/PhysicalHamiltonianNormalizationBridge.lean
MGAP4D/MathlibAnalytic/PhysicalHamiltonianOperatorNormalization.lean
MGAP4D/MathlibAnalytic/InfiniteDimensionalYangMillsRealizationTargets.lean
MGAP4D/MathlibAnalytic/InfiniteDimensionalResidualFillingBridge.lean
MGAP4D/MathlibAnalytic/HardPhysicalResidualHardeningMap.lean
MGAP4D/MathlibAnalytic/CompleteInfiniteDimensionalHilbertConstruction.lean
MGAP4D/MathlibAnalytic/HilbertToPhysicalUnboundedOperatorBridge.lean
MGAP4D/MathlibAnalytic/SelfAdjointHPhysBridgeAdoption.lean
MGAP4D/MathlibAnalytic/SelfAdjointHPhysLaneHardening.lean
MGAP4D/MathlibAnalytic/ContinuumYangMillsLaneHardening.lean
MGAP4D/MathlibAnalytic/PlaquetteSpectralWeightLaneHardening.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianMassGapWitnessHardening.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianMassGapTheorem.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianMassGapReleaseAdoption.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianCompleteMassGapDerivation.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianCompleteMassGapReleaseAdoption.lean
MGAP4D/MathlibAnalytic/FourLaneResidualClosure.lean
MGAP4D/MathlibAnalytic/InternalReviewResidualClosureGate.lean
MGAP4D/MathlibAnalytic/ExternalAuditReadinessGate.lean
```

## CI and audit status

Full local replay is:

```bash
bash scripts/check.sh
```

The replay path currently runs:

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

Confirmed operator-normalization CI checkpoint before merge:

```text
Workflow: Full Local Check CI / Run scripts/check.sh
Workflow run ID: 25992161524
Head commit: a212a163fe98067dee2a3704022d1e9271172554
Result: success
Observed timestamp: 2026-05-17
```

That same head commit had:

```text
Bridge Coherence CI: success
Lean Direct Elan CI: success
External Audit Readiness CI: success
Full Local Check CI: success
```

Current CI and release-surface ledgers:

```text
docs/external_audit_readiness_gate_ci.md
docs/continuum_hamiltonian_complete_release_surface.md
docs/physical_hamiltonian_operator_normalization.md
```

## External review entry points

Start here:

```text
EXTERNAL_AUDIT_PACKET.md
```

Then use:

```text
EXTERNAL_REVIEW_CHECKLIST.md
INDEPENDENT_REPLAY.md
THEOREM_INDEX.md
PHYSICAL_REALIZATION_BOUNDARY.md
docs/physical_hamiltonian_operator_normalization.md
docs/continuum_hamiltonian_complete_release_surface.md
docs/infinite_dimensional_yang_mills_target_layer.md
docs/infinite_dimensional_residual_filling_bridge.md
docs/hard_physical_residual_hardening_map.md
docs/complete_infinite_dimensional_hilbert_construction.md
docs/self_adjoint_hphys_lane_hardening.md
docs/continuum_yang_mills_lane_hardening.md
docs/plaquette_spectral_weight_lane_hardening.md
docs/continuum_hamiltonian_mass_gap_witness_hardening.md
docs/four_lane_residual_closure.md
docs/internal_review_residual_closure_gate.md
docs/external_audit_readiness_gate.md
docs/external_audit_readiness_gate_field_classification.md
docs/external_audit_readiness_replay_certificate.md
docs/external_audit_readiness_gate_ci.md
```

## Review meaning

A successful replay means:

```text
the repository builds with the pinned Lean toolchain and pinned mathlib version
the declared audit scripts pass
the theorem-surface, bridge-surface, target-layer, residual-hardening, physical-Hamiltonian normalization, continuum-Hamiltonian theorem/release, final readiness-gate, field-classification, and replay-certificate checks pass
the replay summary is reproducible
```

A successful replay does not by itself mean:

```text
external mathematical consensus
independent peer-review acceptance
public final theorem acceptance
```
