# Physical Hamiltonian normalization

This note records a pre-Mathlib normalization layer for the physical Hamiltonian surface.

## Lean artifacts

```text
MGAP4D/Hamiltonian/Normalization.lean
MGAP4D/Hamiltonian.lean
```

## Added surface

```text
HamiltonianNormalizationUnit
HamiltonianNormalizationUnit.ready
physicalHamiltonianNormalizationUnit
PhysicalHamiltonianNormalization
PhysicalHamiltonianNormalization.ready
physicalHamiltonian3320Normalization
hamiltonian_normalization_unit_pack
physical_hamiltonian_normalization_pack
physical_hamiltonian_3320_normalization_ready
physical_hamiltonian_3320_normalized_value
physical_hamiltonian_3320_normalization_preserves_positive_numerator
physical_hamiltonian_3320_unit_scale_one
physical_hamiltonian_3320_vacuum_reference_zero
```

## Meaning

The layer records the internal normalized convention for the physical Hamiltonian label `H_phys`.

```text
unit scale = 1
vacuum energy reference = 0
physical gap record uses H_phys
normalized gap value = 33/20
positive numerator evidence is preserved
normalization does not change the witness
```

## Boundary

```text
pre-Mathlib structural normalization only
R1--R7 theorem completions not claimed
Mathlib on main not introduced
public theorem boundary held
```
