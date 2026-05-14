# Hamiltonian normalization pre-release bridge

This note records a pre-Mathlib bridge from physical Hamiltonian normalization into the spectral pre-release checkpoint.

## Lean artifacts

```text
MGAP4D/Hamiltonian/NormalizationPreReleaseBridge.lean
MGAP4D/Hamiltonian.lean
```

## Added surface

```text
HamiltonianNormalizationPreReleaseBridge
HamiltonianNormalizationPreReleaseBridge.ready
hamiltonian3320NormalizationPreReleaseBridge
hamiltonian_normalization_pre_release_bridge_pack
hamiltonian3320_normalization_pre_release_bridge_ready
hamiltonian3320_pre_release_bridge_value
hamiltonian3320_pre_release_bridge_checkpoint_value
hamiltonian3320_pre_release_bridge_preserves_positive_numerator
hamiltonian3320_pre_release_bridge_public_boundary_locked
```

## Meaning

The bridge connects the normalized H_phys surface to the spectral pre-release checkpoint.

```text
Hamiltonian spectral bridge ready
spectral pre-release checkpoint ready
normalized gap matches checkpoint value
physical witness matches checkpoint witness
unit scale = 1
vacuum reference = 0
positive numerator preserved
public boundary locked
```

## Boundary

```text
pre-Mathlib structural pre-release bridge only
R1--R7 theorem completions not claimed
Mathlib on main not introduced
public theorem boundary held
```
