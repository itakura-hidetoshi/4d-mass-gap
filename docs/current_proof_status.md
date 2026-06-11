# Current proof status anchor

This file is the short status anchor for `main` when older open pull requests, README/ROADMAP text, or external summaries lag behind the proof spine.

## Current `main` proof-facing surface

The current proof-facing surface is the carrier / spectral-route / R1--R7 terminal-public-external audit chain:

```text
Basic-layer route marker
  -> abstract exactGapValueReal carrier with positivity / above-one facts
  -> continuum-Hamiltonian / PVM / operator-spectral carrier-alignment route
  -> R6 exact atom 33/20 / spectral-PVM pinning route
  -> R7 positive spectral-weight witness route
  -> R1--R7 terminal discharge chain
  -> public / external audit receipt chain
```

Current public-boundary reading:

```text
internal Lean terminal discharge route: present
public / external audit receipt surface: present
external mathematical consensus: not claimed
independent peer-review completion: not claimed
Clay-style public acceptance: not claimed
```

## Central payload

The central Lean-facing terminal payload remains:

```text
MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20
Plaquette.observableSpectralWeight3320Certificate.massWitness.positiveMass = true
```

The important correction is the origin of the first line: it must not be read as a
Basic-layer, `ExactGapReal.lean`, or pre-R6 definitional unfolding.  The displayed
`33/20` value is exported through the R6 non-definitional spectral/PVM pinning
surface and then carried forward by R7 and the terminal chain.

## Exact-gap layer separation

The current route separates five review layers:

```text
1. Basic-layer route marker
2. downstream real-carrier / positivity-boundary layer
3. continuum-Hamiltonian / PVM / operator-spectral carrier-alignment layer
4. R6 exact atom and R7 positive spectral-weight layer
5. engineering / audit / public-boundary marker layer
```

Correct reading:

```text
Basic.lean
  -> marker-only route-deferred layer
  -> no real-valued gap carrier
  -> no local final-value assignment

ExactGapReal.lean
  -> defines exactGapValueReal as an abstract downstream normalized real carrier
  -> proves exactGapValueReal_pos and exactGapValueReal_above_one
  -> does not provide exactGapValueRealRouteWitness
  -> does not provide exactGapValueReal_eq
  -> does not expose exactGapValueReal = 33/20

ContinuumHamiltonianMassGapTheorem.lean
  -> proves positivity and the continuum value-boundary surface
  -> exposes ContinuumHamiltonianExactValueRequiresR6Pinning
  -> keeps exactGapValueReal = 33/20 gated by R6

YangMillsHamiltonianSpectralDerivation3320.lean
  -> aligns the spectral infimum / attainment / observable atom value with exactGapValueReal
  -> aligns exactGapValueReal with the derived Hamiltonian spectral value
  -> intentionally does not export derivedHamiltonianSpectralValue = 33/20 outside R6

R6 ExactAtom3320 lane
  -> supplies the non-definitional spectral/PVM pinning route for the displayed value

R7 positive-weight lane
  -> supplies the positive spectral-weight witness and preserves the exact value

R1--R7 terminal chain
  -> records exact 33/20 plus positive spectral weight at terminal level
```

## Exact `33/20` derivation source

### 1. Basic-layer marker role

```text
MGAP4D/MathlibAnalytic/Basic.lean
```

Primary anchors:

```text
FourDYangMillsAnalyticGapValueOrigin.ready
four_d_yang_mills_analytic_gap_value_origin_ready
four_d_yang_mills_basic_layer_numeric_carrier_absent
```

### 2. Real-carrier role

```text
MGAP4D/MathlibAnalytic/ExactGapReal.lean
```

Current anchors:

```text
exactGapValueReal
exactGapValueReal_pos
exactGapValueReal_above_one
exactGapValueReal_mem_positive_ray
exactGapValueReal_mem_above_one_ray
exactGapRealSurface
```

There is intentionally no `exactGapValueReal_eq` theorem in this layer.

### 3. Continuum-Hamiltonian / PVM / spectral derivation role

```text
MGAP4D/MathlibAnalytic/ContinuumHamiltonianMassGapTheorem.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianCompleteMassGapDerivation.lean
MGAP4D/MathlibAnalytic/YangMillsHamiltonianSpectralDerivation3320.lean
```

Primary anchors:

```text
ContinuumHamiltonianExactValueRequiresR6Pinning
continuum_hamiltonian_derives_exact_mass_gap_value
physical_4d_ym_continuum_hamiltonian_derives_complete_spectral_exact_mass_gap
physical_4d_ym_continuum_hamiltonian_complete_spectral_derivation_exact_gap
physical_4d_ym_continuum_hamiltonian_complete_spectral_atom_positive_nonzero
yang_mills_hamiltonian_spectral_derivation_3320_ready
yang_mills_hamiltonian_exact_gap_eq_spectral_value
yang_mills_hamiltonian_exact_gap_value_from_physical_spectrum
```

The Yang--Mills spectral interface aligns the derived Hamiltonian spectral value
with `exactGapValueReal`, while its boundary comments and theorem surfaces keep
public / final-release boundary held.

### 4. R6 exact-atom / value-pinning role

```text
MGAP4D/R6/Theorem/ExactAtom3320YangMillsSpectralDerivation.lean
MGAP4D/R6/Theorem/ExactAtom3320NonDefinitionalDerivation.lean
MGAP4D/R6/Theorem/ExactAtom3320SpectralOriginFirewall.lean
MGAP4D/R6/Theorem/ExactAtom3320ValueOriginQuarantine.lean
MGAP4D/R6/Theorem/ExactAtom3320DirectReviewBridge.lean
```

Primary anchors:

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
