# MGAP4D Theorem Index

This index gives an external-review map for the current MGAP4D theorem surfaces.

It is a navigation and audit document. It does not replace Lean kernel checking, mathematical proof review, or the source files themselves.

## Review boundary

The current public claim is an internal normalized theorem-body / proof-architecture surface with explicit replay and audit support.

This index does not claim:

```text
external mathematical consensus
peer-review completion
Clay-style public final theorem acceptance
a dimensional physical mass gap without choosing E0
that audit scripts replace Lean kernel checking
```

The strongest executable check remains:

```bash
bash scripts/check.sh
```

The strongest Lean kernel gate remains:

```bash
lake build
```

For the physical-realization boundary of `PUnit`, singleton, prototype, skeleton, target, construction, and release-adoption surfaces, see:

```text
PHYSICAL_REALIZATION_BOUNDARY.md
```

## Active Lean roots

| Root | Role |
|---|---|
| `MGAP4D.lean` | Top-level Lean import root. |
| `MGAP4D/MathlibAnalytic.lean` | Internal analytic theorem-surface root, importing the complete Hilbert / continuum-Hamiltonian / external-audit readiness route. |

## Major theorem surfaces audited for non-placeholder statements

These theorem surfaces are checked by:

```bash
python3 scripts/audit_major_theorem_nonplaceholder.py
```

The audit verifies that the named theorem statements exist, are not merely trivial `True` placeholders, and contain required anchors such as `33/20`, positivity, spectral weight, PVM mass compatibility, or normalization equations.

| File | Theorem surface | Review role | Required anchor class |
|---|---|---|---|
| `MGAP4D/MathlibAnalytic/ExactGapTheoremBodyClosure.lean` | `exact_gap_theorem_body_closure_value` | Records the exact normalized theorem-body value surface. | `33/20`, `exactGapValueReal`, theorem-body closure anchor. |
| `MGAP4D/MathlibAnalytic/ExactGapTheoremBodyClosure.lean` | `exact_gap_theorem_body_closure_positive` | Records positivity of the exact normalized gap surface. | positivity, `exactGapValueReal`, theorem-body closure anchor. |
| `MGAP4D/MathlibAnalytic/ExactGapTheoremBodyClosure.lean` | `exact_gap_theorem_body_closure_weight_positive` | Records positive observable spectral weight at the exact atom surface. | `observableWeightPositive`, `spectralWeight`, positive-weight anchor. |
| `MGAP4D/MathlibAnalytic/ExactGapTheoremBodyClosure.lean` | `exact_gap_theorem_body_closure_weight_equals_pvm_mass` | Records compatibility between observable spectral weight and PVM mass. | `observableWeightEqualsPVMMass`, `projectionMass`, PVM mass anchor. |
| `MGAP4D/MathlibAnalytic/OperatorMeasureCompatibilityTheorem.lean` | `operator_measure_compatibility_weight_equals_pvm_mass` | Records operator-measure compatibility of constructed observable and exact atom. | `projectionMass`, `spectralWeight`, `constructedObservable`, `exactAtom`. |
| `MGAP4D/MathlibAnalytic/OperatorMeasureCompatibilityTheorem.lean` | `operator_measure_compatibility_positive_weight` | Records positive spectral weight for the constructed observable at the exact atom. | positivity, `spectralWeight`, `constructedObservable`, `exactAtom`. |
| `MGAP4D/MathlibAnalytic/PhysicalHamiltonianNormalizationBridge.lean` | `physical_hamiltonian_normalized_gap_def` | Defines normalized gap from physical gap and reference energy scale. | `normalizedGap`, `physicalGap`, `referenceEnergyScale`. |
| `MGAP4D/MathlibAnalytic/PhysicalHamiltonianNormalizationBridge.lean` | `physical_hamiltonian_gap_reconstruction` | Reconstructs physical gap from reference energy scale and normalized gap. | `physicalGap`, `referenceEnergyScale`, `normalizedGap`. |
| `MGAP4D/MathlibAnalytic/PhysicalHamiltonianNormalizationBridge.lean` | `physical_hamiltonian_normalized_gap_eq_3320` | Connects normalized physical Hamiltonian gap to the exact theorem-body value. | `33/20`, `exactGapValueReal`, `normalizedGap`. |
| `MGAP4D/MathlibAnalytic/ExactValueTheoremBodyOrigin.lean` | `exact_value_origin_from_theorem_body` | Records that the exact value originates from theorem-body structure. | `33/20`, `exactValueFromTheoremBody`, `exactGapValueReal`. |
| `MGAP4D/MathlibAnalytic/ExactValueTheoremBodyOrigin.lean` | `exact_value_origin_not_packaging_artifact` | Records that the exact value is not asserted merely by packaging / release wrapping. | `notPackagingArtifact`. |
| `MGAP4D/MathlibAnalytic/ExactValueTheoremBodyOrigin.lean` | `exact_value_origin_not_ci_ledger_artifact` | Records that the exact value is not asserted merely by CI ledger artifacts. | `notCILedgerArtifact`. |

## Analytic / physical bridge surfaces audited for coherence

These bridge surfaces are checked by:

```bash
python3 scripts/audit_bridge_coherence.py
```

The bridge audit verifies expected import edges, ready surfaces, value anchors, positivity anchors, public-boundary anchors, and infinite-dimensional Yang--Mills target obligations.

| Order | File | Bridge role | Boundary marker class |
|---:|---|---|---|
| 1 | `MGAP4D/MathlibAnalytic/ConcreteHilbertRealizationTheorem.lean` | Concrete Hilbert realization theorem surface. | `infiniteDimensionalPhysicalHilbertStillOpen`, `publicBoundaryHeld`. |
| 2 | `MGAP4D/MathlibAnalytic/ConcreteHPhysRealizationTheorem.lean` | Concrete `H_phys` / unbounded-operator realization theorem surface. | `fullUnboundedPhysicalOperatorStillOpen`, `publicBoundaryHeld`. |
| 3 | `MGAP4D/MathlibAnalytic/PhysicalUnboundedOperatorSkeleton.lean` | Physical unbounded-operator skeleton surface. | `concreteYangMillsHamiltonianStillOpen`, `publicBoundaryHeld`. |
| 4 | `MGAP4D/MathlibAnalytic/ConcreteYangMillsHamiltonianSkeleton.lean` | Concrete Yang-Mills Hamiltonian skeleton surface. | `continuumLimitStillOpen`, `spectralRealizationStillOpen`, `publicBoundaryHeld`. |
| 5 | `MGAP4D/MathlibAnalytic/SpectralRealizationSkeleton.lean` | Spectral/PVM realization skeleton surface. | `continuumSpectralTheoremStillOpen`, `publicBoundaryHeld`. |
| 6 | `MGAP4D/MathlibAnalytic/ContinuumSpectralTheoremSkeleton.lean` | Continuum spectral theorem skeleton surface. | `finalTheoremReleaseStillHeld`, `publicBoundaryHeld`. |
| 7 | `MGAP4D/MathlibAnalytic/PhysicalHamiltonianNormalizationBridge.lean` | Physical Hamiltonian normalization bridge surface. | `theoremBodyUnchanged`, `publicBoundaryHeld`. |
| 8 | `MGAP4D/MathlibAnalytic/InfiniteDimensionalYangMillsRealizationTargets.lean` | Infinite-dimensional Yang--Mills physical realization target / proof-obligation layer. | `publicBoundaryHeld`, `finalReleaseHeld`. |

## Complete Hilbert and continuum-Hamiltonian route

The active hardening route now uses the complete Hilbert lane, not the former `HilbertConstructionLaneHardening` name:

```text
HardPhysicalResidualHardeningMap
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

Important source files:

```text
MGAP4D/MathlibAnalytic/CompleteInfiniteDimensionalHilbertConstruction.lean
MGAP4D/MathlibAnalytic/HilbertToPhysicalUnboundedOperatorBridge.lean
MGAP4D/MathlibAnalytic/SelfAdjointHPhysBridgeAdoption.lean
MGAP4D/MathlibAnalytic/SelfAdjointHPhysLaneHardening.lean
MGAP4D/MathlibAnalytic/ContinuumYangMillsLaneHardening.lean
MGAP4D/MathlibAnalytic/PlaquetteSpectralWeightLaneHardening.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianMassGapWitness.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianExactMassGapDerivation.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianMassGapWitnessHardening.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianMassGapTheorem.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianMassGapReleaseAdoption.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianCompleteMassGapDerivation.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianCompleteMassGapReleaseAdoption.lean
MGAP4D/MathlibAnalytic/FourLaneResidualClosure.lean
MGAP4D/MathlibAnalytic/InternalReviewResidualClosureGate.lean
MGAP4D/MathlibAnalytic/ExternalAuditReadinessGate.lean
```

## Infinite-dimensional Yang--Mills target layer

The target layer is the direct evolution of the previous weakness: instead of hiding the gap between skeletons and full physical analysis, it makes that gap first-class in Lean.

It introduces:

```text
InfiniteDimensionalYangMillsRealizationTarget
InfiniteDimensionalYangMillsRealizationTarget.ready
InfiniteDimensionalYangMillsTargetReviewSurface
infinite_dimensional_yang_mills_target_review_surface_ready
```

The layer requires explicit witnesses for:

```text
infinite-dimensional Hilbert realization
separable Hilbert witness
dense core
domain density
symmetric H_phys
self-adjoint H_phys
gauge-invariant sector
Yang-Mills energy witness
continuum limit
OS positivity
spectral theorem
exact atom
positive plaquette spectral weight
nonempty vacuum-orthogonal sector
normalization preservation
public boundary held
final release held
```

This layer is not a completed public-final physical continuum proof. It is an auditable proof-obligation surface that states what must be supplied before promotion beyond skeleton / contract witnesses.

## Normalization surface

The physical Hamiltonian normalization bridge uses an explicit reference energy scale:

```text
H_norm = H_phys / E0
normalizedGap = physicalGap / E0
physicalGap = E0 * normalizedGap
```

In internal normalized units:

```text
E0 = 1
normalizedGap = exactGapValueReal = 33/20
physicalGap = exactGapValueReal = 33/20
```

Dimensional reading requires an external reference scale:

```text
physicalGap_dimensional = E0 * (33/20)
```

## Audit scripts and expected roles

| Script | Role |
|---|---|
| `scripts/verify_manifest.py` | Checks archived manifest consistency. |
| `scripts/audit_lean_forbidden_tokens.py` | Checks for forbidden Lean tokens outside comments / strings. |
| `scripts/audit_major_theorem_nonplaceholder.py` | Checks named load-bearing theorem surfaces for non-placeholder statements and required anchors. |
| `scripts/audit_bridge_coherence.py` | Checks bridge import edges, ready surfaces, preservation anchors, positivity anchors, infinite-dimensional target obligations, and public-boundary anchors. |
| `scripts/audit_infinite_dimensional_target_layer.py` | Checks infinite-dimensional Yang--Mills target-layer anchors. |
| `scripts/audit_infinite_dimensional_residual_filling.py` | Checks residual-filling bridge anchors. |
| `scripts/audit_hard_physical_residual_hardening_map.py` | Checks hard residual hardening map anchors. |
| `scripts/audit_complete_infinite_dimensional_hilbert_construction.py` | Checks the active complete Hilbert construction lane. |
| `scripts/audit_self_adjoint_hphys_lane_hardening.py` | Checks self-adjoint H_phys hardening anchors. |
| `scripts/audit_continuum_yang_mills_lane_hardening.py` | Checks continuum Yang--Mills hardening anchors. |
| `scripts/audit_plaquette_spectral_weight_lane_hardening.py` | Checks plaquette spectral-weight hardening anchors. |
| `scripts/audit_continuum_hamiltonian_mass_gap_witness_hardening.py` | Checks continuum-Hamiltonian witness hardening anchors. |
| `scripts/audit_four_lane_residual_closure.py` | Checks four-lane residual closure anchors. |
| `scripts/audit_internal_review_residual_closure_gate.py` | Checks internal review residual closure gate anchors. |
| `scripts/audit_external_audit_readiness_gate.py` | Checks external audit readiness gate anchors. |
| `scripts/audit_external_audit_readiness_gate_field_classification.py` | Checks witness field classification. |
| `scripts/audit_external_audit_readiness_replay_certificate.py` | Checks replay certificate anchors. |
| `scripts/replay_summary.py` | Generates a lightweight replay summary. |
| `scripts/check.sh` | Runs the local full replay path. |

## How to use this index in review

Recommended external review order:

1. Run `bash scripts/check.sh`.
2. Inspect the 12 major theorem surfaces listed above.
3. Inspect the 8 bridge / target files listed above.
4. Inspect the complete Hilbert and continuum-Hamiltonian route files listed above.
5. Read `PHYSICAL_REALIZATION_BOUNDARY.md` before interpreting singleton / prototype / skeleton / target / construction surfaces physically.
6. Compare source statements with the corresponding documentation ledgers in `docs/`.
7. Confirm `lake build` on a fresh clone with the pinned `lean-toolchain`.
8. Treat CI and audit success as replay support, not as a substitute for mathematical review.

## Residual boundary

The index intentionally preserves the distinction between:

```text
internal proof-architecture theorem-body closure
contract / bridge / skeleton / construction surfaces
infinite-dimensional physical target obligations
Lean kernel build success
external mathematical consensus
```

A successful replay of this index means that the repository's declared theorem, bridge, target, construction, continuum-Hamiltonian, and external-readiness surfaces are present, auditable, and buildable in the pinned Lean environment.

It does not by itself discharge independent mathematical review of the full physical continuum Yang-Mills mass gap problem.