# Yang--Mills Hamiltonian spectral value alignment before R6

This note documents the additive Lean theorem surface
`MGAP4D.MathlibAnalytic.YangMillsHamiltonianSpectralDerivation3320`.

The file name is legacy, but the contract is now stricter: this upstream layer
must not introduce or derive the concrete numeric value `33/20`.  The concrete
value is reserved for the R6 exact-atom layer.  Upstream of R6, this surface only
records spectral-route alignment around one derived Hamiltonian spectral value.

```text
Yang--Mills continuum Hamiltonian
  -> H_phys from Yang--Mills
  -> self-adjoint / spectral chain
  -> Rayleigh lower-bound surface
  -> Rayleigh attainment surface
  -> positive spectral-mass observable surface
  -> one shared derived Hamiltonian spectral value
  -> no upstream 33/20 claim
```

## Core Lean surface

```text
YangMillsHamiltonianSpectralDerivation3320
yangMillsHamiltonianSpectralDerivation3320
YangMillsHamiltonianSpectralDerivation3320.ready
yang_mills_hamiltonian_spectral_derivation_3320_ready
```

## Spectral alignment anchors

```text
infimum_eq_derived
attainment_eq_derived
atom_eq_derived
yang_mills_hamiltonian_spectral_infimum_eq_derived
yang_mills_hamiltonian_spectral_attainment_eq_derived
yang_mills_hamiltonian_observable_atom_eq_derived
yang_mills_hamiltonian_exact_gap_eq_spectral_value
```

The intended reading is:

```text
spectral infimum value = derived Hamiltonian spectral value
attained spectral value = derived Hamiltonian spectral value
observable spectral atom value = derived Hamiltonian spectral value
exactGapValueReal = derived Hamiltonian spectral value
```

This is not a derivation of `33/20`.  It is a no-numeric upstream carrier and
alignment surface.  R6 is the first layer allowed to state the concrete value.

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

The surface remains theorem-witness-only. It does not claim external mathematical
consensus, peer-review completion, final public theorem acceptance, or upstream
numeric derivation.

## Relation to the existing continuum-Hamiltonian route

The prior route provides a positive mass-gap carrier and a review-ready chain:

```text
continuum_hamiltonian_derives_positive_mass_gap
continuum_hamiltonian_theorem_uses_hardened_witness_bundle
```

The spectral surface adds the explicitly spectral alignment direction:

```text
Rayleigh lower bound + Rayleigh attainment + positive spectral atom
  => one shared derived Hamiltonian spectral value
```

## R6 numeric boundary

The concrete value belongs downstream:

```text
R6 exact atom layer
  => first admissible 33/20 derivation
```

Any statement that `33/20` was already derived in this upstream file should be
treated as stale wording and removed.
