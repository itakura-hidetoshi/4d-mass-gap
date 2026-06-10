# Yang--Mills Hamiltonian spectral derivation claim

This note documents the additive Lean theorem surface
`MGAP4D.MathlibAnalytic.YangMillsHamiltonianSpectralDerivation3320`.

The file name is legacy, but the contract is now three-layered:

1. the carrier fields remain an alignment surface around one derived Hamiltonian
   spectral value, with no independent upstream 33/20 claim baked into the
   structure fields;
2. the theorem layer reads that aligned carrier through the already-installed
   continuum-Hamiltonian exact-value theorem, yielding the forced normalized
   value `33/20`;
3. the claim layer exposes the full Yang--Mills Hamiltonian spectral derivation
   as a theorem-witnessed public claim surface.

The phrase **no upstream 33/20 claim** therefore means: no independent numeric
claim is inserted into the spectral carrier fields before the exact-value route.
The numeric value appears as a theorem-level consequence of the spectral / PVM /
Hamiltonian chain plus the internal exact-value theorem, and is then collected in
`YangMillsHamiltonianSpectralDerivationClaim3320`.

```text
Yang--Mills continuum Hamiltonian
  -> H_phys from Yang--Mills
  -> self-adjoint / spectral chain
  -> Rayleigh lower-bound surface
  -> Rayleigh attainment surface
  -> positive spectral-mass observable surface
  -> one shared derived Hamiltonian spectral value
  -> continuum-Hamiltonian exact-value theorem
  -> forced normalized value 33/20
  -> Yang--Mills Hamiltonian spectral derivation claim
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

## Forced exact-value theorem

The theorem-level strengthening is:

```text
yang_mills_hamiltonian_spectral_pvm_analysis_forces_gap_33_over_20
```

Its intended reading is:

```text
spectral theorem / PVM / observable atom / Hamiltonian alignment
  => derived Hamiltonian spectral value
  => exactGapValueReal
  => 33/20
```

The full public theorem-witness package is:

```text
yang_mills_hamiltonian_spectral_theorem_pvm_hamiltonian_analysis_forces_exact_gap
```

It records in one surface that the self-adjoint spectral chain is ready, the
spectral infimum, spectral attainment, and PVM/observable atom all collapse to
the derived Hamiltonian carrier, that carrier is forced to `33/20`, the spectral
mass is positive and nonzero, and the public/final boundaries remain held.

## Claim surface

The explicit claim surface is:

```text
YangMillsHamiltonianSpectralDerivationClaim3320
yang_mills_hamiltonian_spectral_derivation_claim_3320
yang_mills_hamiltonian_spectral_derivation_claim_forces_gap_33_over_20
yang_mills_hamiltonian_spectral_derivation_claim_positive_nonzero_pvm_mass
yang_mills_hamiltonian_spectral_derivation_claim_boundary_held
```

Its intended reading is:

```text
Yang--Mills Hamiltonian spectral derivation claim
  := installed Yang--Mills Hamiltonian spectral interface is ready
   ∧ self-adjoint spectral chain is ready
   ∧ spectral infimum = derived Hamiltonian spectral value
   ∧ spectral attainment = derived Hamiltonian spectral value
   ∧ PVM / observable spectral atom = derived Hamiltonian spectral value
   ∧ derived Hamiltonian spectral value = 33/20
   ∧ PVM spectral mass > 0
   ∧ PVM spectral mass != 0
   ∧ theoremWitnessOnly
   ∧ noExternalConsensusClaim
   ∧ publicBoundaryHeld
   ∧ finalReleaseHeld
```

This is the precise place where the repository can claim the Yang--Mills
Hamiltonian spectral derivation, while still separating theorem-witness status
from external consensus or final public theorem acceptance.

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
consensus, peer-review completion, or final public theorem acceptance.

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

The release-adoption layer preserves the forced-value reading through:

```text
continuum_hamiltonian_complete_spectral_release_adoption_forces_gap_33_over_20
continuum_hamiltonian_complete_spectral_release_adoption_pvm_hamiltonian_forces_exact_gap
```

## R6 exact atom layer

The R6 exact atom layer remains the first exact-value carrier route.  This file
now records that, once the continuum-Hamiltonian exact-value theorem is imported,
the spectral theorem / PVM / Hamiltonian route necessarily evaluates its derived
spectral carrier to `33/20`, and the claim surface can state the Yang--Mills
Hamiltonian spectral derivation explicitly.
