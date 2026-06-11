# Exact gap layer separation note

This note fixes the external-review distinction around the final normalized mass-gap value.

The current repository separates five review layers:

```text
1. Basic-layer route marker
2. downstream real-carrier / positivity-boundary layer
3. continuum-Hamiltonian / PVM / operator-spectral carrier-alignment layer
4. R6 exact atom and R7 positive spectral-weight route
5. engineering / audit / public-boundary marker layer
```

## Correct current reading

```text
Basic.lean
  -> marker-only route-deferred layer
  -> no real-valued gap carrier
  -> no local final-value assignment

ExactGapReal.lean
  -> defines exactGapValueReal as an abstract normalized real carrier
  -> proves positivity and above-one facts only
  -> does not define, choose, or prove exactGapValueReal = 33/20

Continuum Hamiltonian / PVM / spectral theorem route
  -> aligns the carrier with the Hamiltonian spectral route
  -> carries positivity / nonzero spectral-mass evidence
  -> keeps public / final-release boundary markers visible
  -> keeps the 33/20 value-pinning boundary open before R6

R6 exact-atom route
  -> pins the displayed value 33/20 through the spectral/PVM atom lane
  -> prevents the value from being read as a pre-R6 definitional unfolding

R7 positive-weight route
  -> carries positive spectral weight
  -> preserves exact 33/20 after the R6 value-pinning surface

R1--R7 terminal chain
  -> records exact 33/20 plus positive spectral weight at terminal audit level
```

Thus `exactGapValueReal` is only the normalized carrier.  The displayed equality
`exactGapValueReal = (33 : ℝ) / 20` must be reviewed through the R6 spectral/PVM
pinning surface, not as a definitional or carrier-layer unfolding.

## Current source of the final-value derivation claim

The Basic file is not the source of the derivation claim and does not carry a
real-valued numerical assignment.  `ExactGapReal.lean` also does not carry the
final numeric equality.  The final displayed value is exposed only by the R6
non-definitional spectral/PVM pinning route and then carried forward through R7
and the terminal audit chain.

Primary Lean anchors:

```text
exactGapValueReal
exactGapValueReal_pos
exactGapValueReal_above_one
exact_gap_real_surface_ready
exact_gap_carrier_layer_ready
ContinuumHamiltonianExactValueRequiresR6Pinning
continuum_hamiltonian_derives_exact_mass_gap_value
physical_4d_ym_continuum_hamiltonian_derives_complete_spectral_exact_mass_gap
physical_4d_ym_continuum_hamiltonian_complete_spectral_derivation_exact_gap
yang_mills_hamiltonian_spectral_derivation_3320_ready
yang_mills_hamiltonian_exact_gap_eq_spectral_value
yang_mills_hamiltonian_exact_gap_value_from_physical_spectrum
exact_atom_3320_yang_mills_spectral_derivation_ready
exact_atom_3320_yang_mills_exact_gap_carrier_eq_derived
exact_atom_3320_r6_derived_spectral_value_eq_3320
exact_atom_3320_r6_exact_gap_value_eq_3320
exact_atom_3320_nondefinitional_origin_certificate_ready
exact_atom_3320_nondefinitional_derivation_target_ready
hard_physical_residual_ledger_r1_r7_terminal_exact_value_and_positive_weight
```

## 1. Basic-layer route marker

Lean anchors:

```text
FourDYangMillsAnalyticGapValueOrigin.ready
four_d_yang_mills_analytic_gap_value_origin_ready
four_d_yang_mills_basic_layer_numeric_carrier_absent
```

Policy:

```text
Basic.lean
  contains no final-value literal and no real-valued carrier
  records that the spectral theorem, PVM observable, and Hamiltonian theorem routes are deferred
  records basicLayerNumericCarrierAbsent = true
```

## 2. Downstream real-carrier / positivity-boundary layer

Lean anchors:

```text
exactGapValueReal
exactGapValueReal_pos
exactGapValueReal_above_one
exact_gap_real_surface_ready
exact_gap_carrier_layer_ready
exact_gap_value_derivation_boundary_ready
```

Policy:

```text
ExactGapReal.lean
  introduces exactGapValueReal as an abstract downstream normalized real carrier
  proves positivity and above-one facts
  does not provide exactGapValueRealRouteWitness
  does not provide exactGapValueReal_eq
  does not expose exactGapValueReal = 33/20
```

## 3. Continuum-Hamiltonian / PVM / operator-spectral derivation layer

Lean anchors:

```text
ExactGapSpectralReceiptLayerReady
exact_gap_spectral_receipt_layer_ready
yang_mills_hamiltonian_spectral_derivation_3320_ready
yang_mills_hamiltonian_exact_gap_eq_spectral_value
yang_mills_hamiltonian_exact_gap_value_from_physical_spectrum
physical_4d_ym_continuum_hamiltonian_derives_complete_spectral_exact_mass_gap
physical_4d_ym_continuum_hamiltonian_complete_spectral_derivation_exact_gap
physical_4d_ym_continuum_hamiltonian_complete_spectral_atom_positive_nonzero
```

This layer aligns `exactGapValueReal` with the derived Hamiltonian spectral value.
It deliberately does not export `derivedHamiltonianSpectralValue = 33/20` outside
R6.

## 4. R6 exact-atom / value-pinning role

Lean anchors:

```text
ExactAtom3320R6NormalizedSpectralAtom
ExactAtom3320R6SpectralPVMPinsDerivedValue
exact_atom_3320_r6_derived_spectral_value_eq_3320
exact_atom_3320_r6_exact_gap_value_eq_3320
exact_atom_3320_nondefinitional_origin_certificate_ready
exact_atom_3320_nondefinitional_derivation_target_ready
```

R6 is the review layer that prevents the displayed value `33/20` from being read
as a pre-R6 definitional unfolding.

## 5. R7 / terminal route

R7 and the terminal R1--R7 chain preserve the R6 value-pinning result together
with the positive spectral-weight witness and public/external audit boundary.
