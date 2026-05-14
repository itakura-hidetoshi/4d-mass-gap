# Hamiltonian spectral normalization bridge

This note records a pre-Mathlib bridge between the physical Hamiltonian normalization surface and the spectral core certificate.

## Lean artifacts

```text
MGAP4D/Hamiltonian/SpectralNormalizationBridge.lean
MGAP4D/Hamiltonian.lean
```

## Added surface

```text
HamiltonianSpectralNormalizationBridge
HamiltonianSpectralNormalizationBridge.ready
hamiltonianSpectral3320NormalizationBridge
hamiltonian_spectral_normalization_bridge_pack
hamiltonian_spectral_3320_normalization_bridge_ready
hamiltonian_spectral_3320_bridge_value
hamiltonian_spectral_3320_bridge_core_value
hamiltonian_spectral_3320_bridge_preserves_positive_numerator
hamiltonian_spectral_3320_bridge_unit_scale_one
hamiltonian_spectral_3320_bridge_vacuum_reference_zero
```

## Meaning

The bridge records that the normalized physical Hamiltonian record and the spectral core certificate share the same normalized value and positive witness.

```text
H_phys normalization ready
spectral core certificate ready
normalized gap matches spectral core value
physical record witness matches spectral core witness
unit scale = 1
vacuum reference = 0
positive numerator preserved
```

## Boundary

```text
pre-Mathlib structural bridge only
R1--R7 theorem completions not claimed
Mathlib on main not introduced
public theorem boundary held
```
