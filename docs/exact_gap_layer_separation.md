# Exact gap layer separation note

This note fixes the external-review distinction around the final normalized mass-gap value.

The current repository separates the normalized exact-gap route into five review layers:

```text
1. Basic-layer route marker
2. downstream abstract real-carrier / positivity-boundary layer
3. continuum-Hamiltonian / PVM / operator-spectral carrier-alignment layer
4. R6 exact atom and R7 positive spectral-weight route
5. engineering / audit / public-boundary marker layer
```

It also contains a separate axiomatic / OS-Wightman / Euclidean construction bridge route. That route is important for physical interpretation, but it must not be confused with the exact `33/20` carrier-layer separation described here.

The central rule is:

```text
33/20 is not a Basic-layer value.
33/20 is not an ExactGapReal.lean definitional value.
33/20 is adopted through the R6 Hamiltonian/PVM/spectral value-pinning route and preserved by R7 and the terminal R1--R7 chain.
```

---

## Correct current reading

```text
Basic.lean
  -> marker-only route-deferred layer
  -> no real-valued gap carrier
  -> no local final-value assignment

ExactGapReal.lean
  -> defines exactGapValueReal as an abstract normalized real carrier
  -> proves positivity and above-one facts only
  -> proves positive-ray and above-one-ray membership consequences
  -> does not define, choose, or prove exactGapValueReal = 33/20

Continuum Hamiltonian / PVM / spectral theorem route
  -> aligns the carrier with the Hamiltonian spectral route
  -> carries positivity / nonzero spectral-mass evidence
  -> keeps public / final-release boundary markers visible
  -> keeps the 33/20 value-pinning boundary routed to R6

R6 exact-atom route
  -> pins the displayed value 33/20 through the Hamiltonian/PVM/spectral atom lane
  -> exposes exact_atom_3320_r6_exact_gap_value_eq_3320_ready
  -> prevents the value from being read as a pre-R6 definitional unfolding

R7 positive-weight route
  -> carries positive spectral weight
  -> preserves exact 33/20 after the R6 value-pinning surface

R1--R7 terminal chain
  -> records exact 33/20 plus positive spectral weight at terminal audit level
  -> also records final-release hold and public-boundary lock
```

Thus `exactGapValueReal` is only the normalized carrier. The displayed equality
`exactGapValueReal = (33 : ℝ) / 20` must be reviewed through the R6 spectral/PVM
pinning surface and the terminal chain, not as a definitional or carrier-layer
unfolding.

---

## Current source of the final-value derivation claim

The Basic file is not the source of the derivation claim and does not carry a real-valued numerical assignment. `ExactGapReal.lean` also does not carry the final numeric equality. The final displayed value is exposed by the R6 non-definitional Hamiltonian/PVM/spectral pinning route and then carried forward through R7 and the terminal audit chain.

Primary Lean anchors:

```text
four_d_yang_mills_basic_layer_numeric_carrier_absent
exactGapValueReal
exactGapValueReal_pos
exactGapValueReal_above_one
exact_gap_real_surface_ready
ContinuumHamiltonianExactValueRequiresR6Pinning
yang_mills_hamiltonian_spectral_derivation_3320_ready
yang_mills_hamiltonian_exact_gap_eq_spectral_value
yang_mills_hamiltonian_exact_gap_value_from_physical_spectrum
yang_mills_hamiltonian_spectral_pvm_analysis_requires_r6_value_pinning
exact_atom_3320_yang_mills_spectral_derivation_ready
exact_atom_3320_yang_mills_exact_gap_carrier_eq_derived
exact_atom_3320_r6_spectral_pvm_pins_derived_value_ready
exact_atom_3320_r6_derived_spectral_value_from_hamiltonian_pvm_route
exact_atom_3320_r6_derived_spectral_value_eq_3320_ready
exact_atom_3320_r6_exact_gap_value_eq_3320_ready
exact_atom_3320_nondefinitional_origin_certificate_ready
exact_atom_3320_nondefinitional_derivation_target_ready
hard_physical_residual_ledger_r1_r7_terminal_exact_value_and_positive_weight
hard_physical_residual_ledger_r1_r7_terminal_final_release_held
hard_physical_residual_ledger_r1_r7_terminal_public_boundary_locked
```

---

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
  cannot be cited as the source of exactGapValueReal = 33/20
```

Reviewer action:

```text
Use Basic.lean only as a route marker.
Do not search for the final numerical value in this layer.
Do not promote the Basic marker into a spectral theorem.
```

---

## 2. Downstream real-carrier / positivity-boundary layer

Lean anchors:

```text
exactGapValueReal
exactGapValueReal_pos
exactGapValueReal_above_one
exactGapValueReal_mem_positive_ray
exactGapValueReal_mem_above_one_ray
exact_gap_real_surface_ready
exact_gap_carrier_layer_ready
exact_gap_value_derivation_boundary_ready
```

Policy:

```text
ExactGapReal.lean
  introduces exactGapValueReal as an abstract downstream normalized real carrier
  proves positivity and above-one facts
  proves positive-ray and above-one-ray membership consequences
  does not provide exactGapValueRealRouteWitness
  does not provide exactGapValueReal_eq
  does not expose exactGapValueReal = 33/20
```

Reviewer action:

```text
Accept ExactGapReal.lean as the normalized carrier layer.
Do not treat it as a closed-form value derivation.
Trace any exact 33/20 claim downstream to R6 and the terminal chain.
```

---

## 3. Continuum-Hamiltonian / PVM / operator-spectral derivation layer

Lean anchors:

```text
ExactGapSpectralReceiptLayerReady
exact_gap_spectral_receipt_layer_ready
yang_mills_hamiltonian_spectral_derivation_3320_ready
yang_mills_hamiltonian_exact_gap_eq_spectral_value
yang_mills_hamiltonian_exact_gap_value_from_physical_spectrum
yang_mills_hamiltonian_spectral_pvm_analysis_requires_r6_value_pinning
physical_4d_ym_continuum_hamiltonian_derives_complete_spectral_exact_mass_gap
physical_4d_ym_continuum_hamiltonian_complete_spectral_derivation_exact_gap
physical_4d_ym_continuum_hamiltonian_complete_spectral_atom_positive_nonzero
```

Policy:

```text
This layer aligns exactGapValueReal with the derived Hamiltonian spectral value.
It preserves positive and nonzero spectral-mass information.
It routes final-value adoption through R6 rather than through Basic.lean or ExactGapReal.lean.
It keeps public-boundary and final-release markers visible.
```

Reviewer action:

```text
Review definitions, assumptions, and dependency chain.
Classify theoremWitnessOnly / ready / receipt surfaces before public promotion.
Do not use this pre-R6 layer alone as the final 33/20 theorem.
```

---

## 4. R6 exact-atom / value-pinning role

Lean anchors:

```text
ExactAtom3320R6NormalizedSpectralAtom
ExactAtom3320R6SpectralPVMPinsDerivedValue
exact_atom_3320_yang_mills_spectral_derivation_ready
exact_atom_3320_yang_mills_exact_gap_carrier_eq_derived
exact_atom_3320_r6_spectral_pvm_pins_derived_value_ready
exact_atom_3320_r6_derived_spectral_value_from_hamiltonian_pvm_route
exact_atom_3320_r6_derived_spectral_value_eq_3320
exact_atom_3320_r6_derived_spectral_value_eq_3320_ready
exact_atom_3320_r6_exact_gap_value_eq_3320
exact_atom_3320_r6_exact_gap_value_eq_3320_ready
exact_atom_3320_nondefinitional_origin_certificate_ready
exact_atom_3320_nondefinitional_derivation_target_ready
```

Policy:

```text
R6 is the layer where the displayed value 33/20 is pinned.
The pinning route is Hamiltonian/PVM/spectral/atom-based.
The exact value theorem is not obtained by unfolding exactGapValueReal.
The canonical ready theorem is exported as exact_atom_3320_r6_exact_gap_value_eq_3320_ready.
```

Representative theorem:

```lean
theorem exact_atom_3320_r6_exact_gap_value_eq_3320_ready :
    MGAP4D.MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20
```

Reviewer action:

```text
Inspect the Hamiltonian/PVM/spectral pinning route.
Inspect the singleton atom route.
Inspect the carrier-alignment theorem from the Yang--Mills spectral layer.
Then inspect how R7 and the terminal chain carry this value forward.
```

---

## 5. R7 / terminal route

Lean anchors:

```text
atom_exact_r6_direct_positive_weight_review_surface_payload
hard_physical_residual_ledger_r6_exact_atom_discharged_r7_positive_weight_closure_3320_ready
hard_physical_residual_ledger_r1_r7_terminal_discharge_chain_index_3320_ready
hard_physical_residual_ledger_r1_r7_terminal_exact_value_and_positive_weight
hard_physical_residual_ledger_r1_r7_terminal_final_release_held
hard_physical_residual_ledger_r1_r7_terminal_public_boundary_locked
hard_physical_residual_ledger_r1_r7_terminal_carries_r4_genuine_pvm_laws
```

Policy:

```text
R7 preserves the exact value and adds the positive spectral-weight witness.
The terminal R1--R7 chain records exact 33/20 and positive weight at audit level.
The terminal chain is a Lean-visible audit chain, not external mathematical acceptance by itself.
Final-release hold and public-boundary lock remain visible.
```

Representative theorem:

```lean
theorem hard_physical_residual_ledger_r1_r7_terminal_exact_value_and_positive_weight :
    MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 ∧
      Plaquette.observableSpectralWeight3320Certificate.massWitness.positiveMass = true
```

Reviewer action:

```text
Accept the terminal chain as the current internal Lean terminal-audit surface.
Do not treat the terminal receipt alone as independent peer review.
Trace all dependencies back through R6, the spectral route, R4/R5, R2/R3, and placeholder inventory.
```

---

## Relation to the OS/Wightman and Euclidean construction bridge

The OS/Wightman and Euclidean construction files should be read as a separate physical-realization / construction-target route:

```text
AxiomaticYangMillsMassGapClosure.lean
OSWightmanHamiltonianReconstructionSpine.lean
OSWightmanMassGapDefinitionBridge.lean
OSWightmanMassGapExternalAuditBridge.lean
EuclideanYangMillsMeasureToMassGapPipeline.lean
EuclideanYangMillsMeasureUnconditionalTarget.lean
EuclideanYangMillsMeasureConstructionSpine.lean
EuclideanYangMillsMeasureConstructionExternalAuditBridge.lean
```

This route records conditional theorem targets and external audit projections. It does not alter the central exact-gap separation rule:

```text
Basic.lean and ExactGapReal.lean are not the source of 33/20.
The normalized value route goes through Hamiltonian/PVM/spectral alignment and R6.
The construction bridge must still be reviewed as a construction bridge, not as external acceptance.
```

For details, read:

```text
docs/axiomatic_yang_mills_mass_gap_closure.md
```

---

## Proof-debt firewall

The layer separation note must be read together with:

```text
docs/proof_placeholder_inventory.md
scripts/audit_proof_placeholder_inventory.py
```

Current firewall:

```text
PUnit
  -> placeholder carrier / target-API shell
  -> open proof debt unless replaced or explicitly superseded

True
  -> metadata / visibility / non-promotion marker
  -> open proof debt for analytic content unless paired with a substantive theorem

StillOpen
  -> active or historical open-obligation marker
  -> must be classified as active, historical, or superseded

theoremWitnessOnly / ready / receipt / packet / manifest
  -> provenance or review-order surface unless payload contains a substantive typed theorem
```

A public route that depends essentially on these markers without a typed replacement theorem remains **not yet discharged** at the analytic proof level.

---

## Physical normalization boundary

The exact value is normalized and dimensionless:

```text
Delta_norm = 33/20
Delta_phys(E0) = E0 * (33/20)
```

`E0` is an external positive reference scale. In internal normalized units, `E0 = 1`.

---

## Public wording boundary

Use:

```text
MGAP4D currently provides a Lean 4 proof-carrying and replayable audit surface for
a normalized 4D mass-gap route. The internal R1--R7 terminal chain records exact
value 33/20 and a positive spectral-weight witness. The repository also exposes
conditional axiomatic / OS-Wightman / Euclidean construction bridge surfaces.
External mathematical consensus and Clay-style public acceptance remain separate
review processes.
```

Do not say:

```text
Basic.lean proves 33/20.
ExactGapReal.lean proves exactGapValueReal = 33/20.
Pre-R6 spectral alignment alone is the final public theorem.
The OS/Wightman / Euclidean construction bridge is an unconditional physical construction by itself.
Terminal receipts replace dependency review.
CI success equals external mathematical consensus.
Clay-style public acceptance has completed.
```
