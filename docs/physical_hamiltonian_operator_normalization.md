# Physical Hamiltonian Operator Normalization

Lean source:

```text
MGAP4D/MathlibAnalytic/PhysicalHamiltonianOperatorNormalization.lean
```

This surface makes the physical Hamiltonian normalization explicit at operator-scale level while keeping the numeric `33/20` theorem outside this pre-R6 layer.

## Convention

```text
H_norm = E0^{-1} * H_phys
H_phys = E0 * H_norm
```

The corresponding gap reading is:

```text
Delta_norm = exactGapValueReal
Delta_phys(E0) = E0 * Delta_norm
Delta_phys(E0) = E0 * exactGapValueReal
```

In MGAP4D internal normalized units:

```text
E0 = 1
Delta_phys(1) = exactGapValueReal
```

The arithmetic normalization of this exact carrier to `33/20` is reserved for the R6 spectral-origin layer.

## Anchors

```text
PhysicalHamiltonianOperatorNormalizationData
physicalHamiltonianOperatorNormalizationData
PhysicalHamiltonianOperatorNormalizationData.ready
physical_hamiltonian_operator_normalization_ready
physical_hamiltonian_operator_normalized_scale_def
physical_hamiltonian_operator_scale_reconstruction
physical_hamiltonian_operator_normalized_gap_eq_exact
physical_hamiltonian_operator_dimensional_gap_eq_reference_mul_exact
physical_hamiltonian_operator_internal_dimensional_gap_eq_exact
```

## Boundary

This is a normalization layer. It does not change:

```text
the theorem body
the spectral/PVM witness
the plaquette witness
the public release gate
the external audit boundary
the external-consensus boundary
```
