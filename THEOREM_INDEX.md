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

For the physical-realization boundary of `PUnit`, singleton, prototype, and skeleton surfaces, see:

```text
PHYSICAL_REALIZATION_BOUNDARY.md
```

## Active Lean roots

| Root | Role |
|---|---|
| `MGAP4D.lean` | Top-level Lean import root. |
| `MGAP4D/MathlibAnalytic.lean` | Internal analytic theorem-surface root. |

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

The bridge audit verifies expected import edges, ready surfaces, value anchors, positivity anchors, and public-boundary anchors.

| Order | File | Bridge role | Boundary marker class |
|---:|---|---|---|
| 1 | `MGAP4D/MathlibAnalytic/ConcreteHilbertRealizationTheorem.lean` | Concrete Hilbert realization theorem surface. | `infiniteDimensionalPhysicalHilbertStillOpen`, `publicBoundaryHeld`. |
| 2 | `MGAP4D/MathlibAnalytic/ConcreteHPhysRealizationTheorem.lean` | Concrete `H_phys` / unbounded-operator realization theorem surface. | `fullUnboundedPhysicalOperatorStillOpen`, `publicBoundaryHeld`. |
| 3 | `MGAP4D/MathlibAnalytic/PhysicalUnboundedOperatorSkeleton.lean` | Physical unbounded-operator skeleton surface. | `concreteYangMillsHamiltonianStillOpen`, `publicBoundaryHeld`. |
| 4 | `MGAP4D/MathlibAnalytic/ConcreteYangMillsHamiltonianSkeleton.lean` | Concrete Yang-Mills Hamiltonian skeleton surface. | `continuumLimitStillOpen`, `spectralRealizationStillOpen`, `publicBoundaryHeld`. |
| 5 | `MGAP4D/MathlibAnalytic/SpectralRealizationSkeleton.lean` | Spectral/PVM realization skeleton surface. | `continuumSpectralTheoremStillOpen`, `publicBoundaryHeld`. |
| 6 | `MGAP4D/MathlibAnalytic/ContinuumSpectralTheoremSkeleton.lean` | Continuum spectral theorem skeleton surface. | `finalTheoremReleaseStillHeld`, `publicBoundaryHeld`. |
| 7 | `MGAP4D/MathlibAnalytic/PhysicalHamiltonianNormalizationBridge.lean` | Physical Hamiltonian normalization bridge surface. | `theoremBodyUnchanged`, `publicBoundaryHeld`. |

## Ordered bridge chain

The expected review chain is:

```text
Concrete Hilbert realization
  -> Concrete H_phys / unbounded-operator realization
  -> Physical unbounded-operator skeleton
  -> Concrete Yang-Mills Hamiltonian skeleton
  -> Spectral/PVM realization skeleton
  -> Continuum spectral theorem skeleton
  -> Final theorem release skeleton / closure
  -> Concrete residual closure
  -> Physical Hamiltonian normalization bridge
  -> Exact value theorem-body origin certificate
```

The bridge-coherence audit currently checks ordered import edges including:

```text
ConcreteHPhysRealizationTheorem imports ConcreteHilbertRealizationTheorem
ConcreteYangMillsHamiltonianSkeleton imports PhysicalUnboundedOperatorSkeleton
SpectralRealizationSkeleton imports ConcreteYangMillsHamiltonianSkeleton
ContinuumSpectralTheoremSkeleton imports SpectralRealizationSkeleton
```

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
| `scripts/audit_bridge_coherence.py` | Checks bridge import edges, ready surfaces, preservation anchors, positivity anchors, and public-boundary anchors. |
| `scripts/replay_summary.py` | Generates a lightweight replay summary. |
| `scripts/check.sh` | Runs the local full replay path. |

## How to use this index in review

Recommended external review order:

1. Run `bash scripts/check.sh`.
2. Inspect the 12 major theorem surfaces listed above.
3. Inspect the 7 bridge files listed above.
4. Read `PHYSICAL_REALIZATION_BOUNDARY.md` before interpreting singleton / prototype / skeleton surfaces physically.
5. Compare source statements with the corresponding documentation ledgers in `docs/`.
6. Confirm `lake build` on a fresh clone with the pinned `lean-toolchain`.
7. Treat CI and audit success as replay support, not as a substitute for mathematical review.

## Residual boundary

The index intentionally preserves the distinction between:

```text
internal proof-architecture theorem-body closure
contract / bridge / skeleton surfaces
Lean kernel build success
external mathematical consensus
```

A successful replay of this index means that the repository's declared theorem and bridge surfaces are present, auditable, and buildable in the pinned Lean environment.

It does not by itself discharge independent mathematical review of the full physical continuum Yang-Mills mass gap problem.
