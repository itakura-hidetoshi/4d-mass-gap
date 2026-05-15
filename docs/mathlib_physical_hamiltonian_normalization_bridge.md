# Mathlib physical Hamiltonian normalization bridge

Branch: main

This note records the standard interpretation bridge for the physical Hamiltonian normalization.

## Lean artifacts

```text
MGAP4D/MathlibAnalytic/PhysicalHamiltonianNormalizationBridge.lean
MGAP4D/MathlibAnalytic.lean
```

## Standard reading

The theorem chain works in dimensionless internal normalized units.

```text
H_norm = H_phys / E0
normalizedGap = physicalGap / E0
physicalGap = E0 * normalizedGap
```

where `E0` is a positive reference energy scale.

In MGAP4D internal normalized units:

```text
E0 = 1
normalizedGap = exactGapValueReal = 33/20
physicalGap = exactGapValueReal = 33/20
```

For dimensional interpretation:

```text
physicalGap_dimensional = E0 * (33/20)
```

Thus `33/20` should be read as the dimensionless spectral gap of the normalized physical Hamiltonian.  The dimensional physical gap is obtained only after choosing the external reference energy scale `E0`.

## Added surface

```text
MathlibAnalytic.PhysicalHamiltonianNormalizationBridgeData
MathlibAnalytic.PhysicalHamiltonianNormalizationBridgeData.ready
MathlibAnalytic.physical_hamiltonian_normalization_scale_positive
MathlibAnalytic.physical_hamiltonian_normalized_gap_def
MathlibAnalytic.physical_hamiltonian_gap_reconstruction
MathlibAnalytic.physical_hamiltonian_internal_reference_scale_eq_one
MathlibAnalytic.physical_hamiltonian_normalized_gap_eq_3320
MathlibAnalytic.prototypePhysicalHamiltonianNormalizationBridgeData
MathlibAnalytic.prototype_physical_hamiltonian_normalization_bridge_ready
MathlibAnalytic.PhysicalHamiltonianNormalizationBridgeReviewSurface
MathlibAnalytic.PhysicalHamiltonianNormalizationBridgeReviewSurface.ready
MathlibAnalytic.physicalHamiltonianNormalizationBridgeReviewSurface
MathlibAnalytic.physical_hamiltonian_normalization_bridge_review_surface_ready
```

## Meaning

```text
physical Hamiltonian normalization is now standard-readable
reference energy scale E0 is explicit and positive
normalized Hamiltonian convention is explicit
dimensionless exact gap is 33/20
physical dimensional gap is E0 * 33/20
the theorem body is unchanged
public theorem boundary is held
```

## Boundary

```text
normalization bridge only
no change to spectral theorem body
no change to PVM body
no change to concrete residual closure
external consensus is not claimed
public theorem boundary held
```
