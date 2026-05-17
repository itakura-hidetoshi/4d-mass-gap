# Yang--Mills Hamiltonian spectral derivation of 33/20

This note documents the additive Lean theorem surface
`MGAP4D.MathlibAnalytic.YangMillsHamiltonianSpectralDerivation3320`.

The purpose is to make the direction of the exact value explicit:

```text
Yang--Mills continuum Hamiltonian
  -> H_phys from Yang--Mills
  -> self-adjoint / spectral chain
  -> Rayleigh lower-bound surface
  -> Rayleigh attainment surface
  -> positive spectral-mass observable surface
  -> derived Hamiltonian spectral value = 33/20
```

## Core Lean surface

```text
YangMillsHamiltonianSpectralDerivation3320
yangMillsHamiltonianSpectralDerivation3320
YangMillsHamiltonianSpectralDerivation3320.ready
yang_mills_hamiltonian_spectral_derivation_3320_ready
```

## Spectral derivation anchors

```text
yang_mills_hamiltonian_spectral_infimum_eq_3320
yang_mills_hamiltonian_spectral_attainment_eq_3320
yang_mills_hamiltonian_observable_atom_eq_3320
yang_mills_hamiltonian_spectral_analysis_derives_3320
yang_mills_hamiltonian_exact_gap_eq_spectral_value
yang_mills_hamiltonian_spectral_derivation_exact_gap_value
```

The intended reading is:

```text
spectral infimum value = 33/20
attained spectral value = 33/20
observable spectral atom value = 33/20
derived Hamiltonian spectral value = 33/20
exactGapValueReal = derived Hamiltonian spectral value
therefore exactGapValueReal = 33/20
```

## Positive spectral mass anchors

```text
yang_mills_hamiltonian_spectral_derivation_positive_mass
yang_mills_hamiltonian_spectral_derivation_nonzero_mass
```

These connect the observable spectral atom surface to positive/nonzero spectral mass.

## Boundary anchors

```text
yang_mills_hamiltonian_spectral_derivation_public_boundary_held
yang_mills_hamiltonian_spectral_derivation_final_release_held
```

The surface remains theorem-witness-only. It does not claim external mathematical consensus, peer-review completion, or final public theorem acceptance.

## Relation to the existing continuum-Hamiltonian route

The prior route already provided:

```text
continuum_hamiltonian_derives_exact_mass_gap_value
continuum_hamiltonian_theorem_uses_hardened_witness_bundle
```

The new surface adds the explicitly spectral direction:

```text
Rayleigh lower bound + Rayleigh attainment + positive spectral atom
  => derived Hamiltonian spectral value = 33/20
```

## Physical normalization boundary

This remains the normalized theorem-body value:

```text
Delta_norm = 33/20
```

A dimensional reading still requires an external reference scale:

```text
Delta_phys(E0) = E0 * (33/20)
```
