# Current proof status anchor

This file is the short status anchor for `main` when older pull requests, README/ROADMAP text, external summaries, or citation snapshots lag behind the proof spine.

## Current `main` proof-facing surface

The current proof-facing surface is a carrier / spectral-route / R1--R7 terminal-audit chain:

```text
Basic-layer route marker
  -> abstract normalized exactGapValueReal carrier with positivity / above-one facts
  -> continuum-Hamiltonian / PVM / operator-spectral carrier-alignment route
  -> R6 exact atom 33/20 / spectral-PVM value-pinning route
  -> R7 positive spectral-weight witness route
  -> R1--R7 terminal audit chain
  -> public / external audit receipt chain
```

Current public-boundary reading:

```text
internal Lean terminal audit route: present
public / external audit receipt surface: present
external mathematical consensus: not claimed
independent peer-review completion: not claimed
Clay-style public acceptance: not claimed
complete public solution of the 4D Yang--Mills mass-gap problem: not claimed
```

This status file is a documentation anchor only. The Lean source tree and theorem bodies remain authoritative.

---

## Central terminal payload

The central terminal-audit payload currently exposed by the R1--R7 chain is:

```text
MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20
Plaquette.observableSpectralWeight3320Certificate.massWitness.positiveMass = true
```

The important correction is the origin of the first line: it must not be read as a Basic-layer theorem, an `ExactGapReal.lean` theorem, or a pre-R6 definitional unfolding. The displayed `33/20` value is adopted through the R6 non-definitional spectral/PVM value-pinning surface and then carried forward by R7 and the terminal chain.

---

## Exact-gap layer separation

The current route separates five review layers:

```text
1. Basic-layer route marker
2. downstream abstract real-carrier / positivity-boundary layer
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
  -> proves ray-membership consequences
  -> does not provide exactGapValueRealRouteWitness
  -> does not provide exactGapValueReal_eq
  -> does not expose exactGapValueReal = 33/20

ContinuumHamiltonianMassGapTheorem.lean and related Hamiltonian files
  -> provide continuum-Hamiltonian / spectral-chain readiness surfaces
  -> preserve positivity and nonzero spectral-mass information
  -> expose boundary markers that require R6 pinning for the displayed exact value

YangMillsHamiltonianSpectralDerivation3320.lean
  -> aligns the spectral infimum / attainment / observable atom value with the derived spectral value
  -> aligns exactGapValueReal with the derived Hamiltonian spectral value
  -> intentionally does not export derivedHamiltonianSpectralValue = 33/20 outside R6

R6 ExactAtom3320 lane
  -> supplies the non-definitional spectral/PVM pinning route for the displayed value

R7 positive-weight lane
  -> supplies the positive spectral-weight witness and preserves the exact value

R1--R7 terminal chain
  -> records exact 33/20 plus positive spectral weight at terminal audit level
```

---

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

Current status:

```text
Basic.lean is a route marker.
It records that the spectral theorem, PVM observable, and Hamiltonian theorem routes are deferred.
It explicitly records basicLayerNumericCarrierAbsent = true.
It is not a numerical exact-gap source.
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
exact_gap_real_surface_ready
```

Current status:

```text
ExactGapReal.lean introduces an abstract normalized real carrier.
It proves positivity and above-one facts.
It does not contain exactGapValueReal_eq.
It does not choose 33/20.
It does not expose exactGapValueReal = (33 : ℝ) / 20.
```

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
yang_mills_hamiltonian_spectral_pvm_analysis_requires_r6_value_pinning
```

Current status:

```text
The Yang--Mills spectral interface aligns exactGapValueReal with the derived Hamiltonian spectral value.
It preserves positive and nonzero spectral-mass surfaces.
It keeps public / final-release boundary markers visible.
It deliberately does not export derivedHamiltonianSpectralValue = 33/20 outside R6.
```

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

Current status:

```text
R6 is the review layer that prevents the displayed value 33/20 from being read as a pre-R6 definitional unfolding.
The exact value theorem is obtained by carrier alignment plus spectral/PVM pinning, not by unfolding ExactGapReal.lean.
```

### 5. R7 / terminal role

```text
MGAP4D/R7/Theorem.lean
MGAP4D/HardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex.lean
MGAP4D/HardPhysicalResidualLedgerR1R7ExternalAuditReceiptChainIndex.lean
```

Primary anchors:

```text
atom_exact_r6_direct_positive_weight_review_surface_payload
hard_physical_residual_ledger_r1_r7_terminal_discharge_chain_index_3320_ready
hard_physical_residual_ledger_r1_r7_terminal_exact_value_and_positive_weight
hard_physical_residual_ledger_r1_r7_terminal_final_release_held
hard_physical_residual_ledger_r1_r7_terminal_public_boundary_locked
```

Current status:

```text
R7 preserves the R6 exact value together with the positive spectral-weight witness.
The terminal R1--R7 chain records exact 33/20 and positive weight at the terminal audit level.
The same terminal layer keeps final-release hold and public-boundary lock visible.
```

---

## Proof-debt reading rule

Do not read a terminal-looking chain as external mathematical acceptance until the dependency chain has been reviewed.

```text
PUnit
  -> placeholder carrier / target-API shell
  -> open proof debt unless replaced or superseded by a typed theorem

True
  -> metadata / visibility / non-promotion flag
  -> cannot close analytic content by itself

StillOpen
  -> active or historical open-obligation marker
  -> must be classified as active, historical, or superseded

theoremWitnessOnly / ready / receipt / packet / manifest
  -> provenance or review-order evidence unless the payload contains a substantive typed theorem
```

Primary inventory:

```text
docs/proof_placeholder_inventory.md
scripts/audit_proof_placeholder_inventory.py
```

---

## Physical normalization boundary

The internal value is normalized and dimensionless:

```text
Delta_norm = 33/20
Delta_phys(E0) = E0 * (33/20)
```

A dimensional physical mass gap requires a positive external reference scale `E0`. In internal normalized units, `E0 = 1`.

---

## Public status sentence

Use this wording for public summaries:

```text
MGAP4D currently provides a Lean 4 proof-carrying and replayable audit surface for
a normalized 4D mass-gap route. The internal R1--R7 terminal chain records exact
value 33/20 and a positive spectral-weight witness. External mathematical
consensus and Clay-style public acceptance remain separate review processes.
```
