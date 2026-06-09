# Continuum Hamiltonian witness provenance map

This note explains how the `ContinuumHamiltonianMassGapWitnessData` receipt slots should be reviewed.

The witness object is not meant to be read as a collection of opaque `Prop` assumptions. Each non-boundary slot is now paired with an explicit theorem anchor in:

```text
MGAP4D/MathlibAnalytic/ContinuumHamiltonianMassGapWitnessProvenance.lean
```

The purpose is to make the external-review question precise:

```text
not merely:  does a receipt slot exist?
but rather: from which concrete theorem / construction / spectral route does this slot arise?
```

## Slot provenance table

| Witness slot | Provenance theorem anchor | Source route |
|---|---|---|
| `physicalContinuumHamiltonianReady` | `continuum_hamiltonian_witness_physical_surface_provenance` | `continuum_ym_concrete_skeleton_hardened` from `ContinuumYangMillsLaneHardening.lean` |
| `hphysFromContinuumYMReady` | `continuum_hamiltonian_witness_hphys_from_ym_provenance` | `continuum_ym_hphys_built_from_ym_hardened` from `ContinuumYangMillsLaneHardening.lean` |
| `selfAdjointSpectralChainReady` | `continuum_hamiltonian_witness_self_adjoint_spectral_slot_provenance` | `self_adjoint_hphys_lane_hardening_ready`, `spectral_realization_skeleton_review_surface_ready`, `continuum_spectral_theorem_skeleton_review_surface_ready` |
| `normalizationToExactGapReady` | `continuum_hamiltonian_witness_normalization_slot_provenance` | `physical_hamiltonian_normalization_bridge_review_surface_ready` plus carrier equality |
| `compactCenteredPlaquetteWeightReady` | `continuum_hamiltonian_witness_compact_plaquette_provenance` | `plaquette_weight_compact_support_hardened`, `plaquette_weight_centered_hardened`, `plaquette_weight_smeared_hardened` |
| `spectralMassObservableReady` | `continuum_hamiltonian_witness_spectral_mass_observable_provenance` | `plaquette_weight_observable_atom_hardened`, `plaquette_weight_positive_weight_hardened`, `plaquette_weight_nonzero_weight_hardened` |
| `massGapDerivationWitness` | `continuum_hamiltonian_witness_mass_gap_derivation_slot_provenance` | `continuum_hamiltonian_derives_positive_mass_gap` plus `physical_4d_ym_continuum_hamiltonian_complete_spectral_derivation_exact_gap` |
| `continuumHamiltonianToMassGapChainReady` | `continuum_hamiltonian_witness_chain_slot_provenance` | `continuum_yang_mills_lane_hardening_ready` and `plaquette_spectral_weight_lane_hardening_ready` |

## Exact-value provenance

The normalized carrier remains:

```text
exactGapValueReal : ℝ := 33 / 20
```

The local carrier files are:

```text
MGAP4D/MathlibAnalytic/Basic.lean
MGAP4D/MathlibAnalytic/ExactGapReal.lean
```

These files only install and check the carrier. They are not the source of the spectral derivation.

The derivation receipt is:

```text
continuum_hamiltonian_witness_exact_value_derivation_provenance
```

which points to:

```text
physical_4d_ym_continuum_hamiltonian_complete_spectral_derivation_exact_gap
```

and thereby to the spectral derivation route in:

```text
MGAP4D/MathlibAnalytic/YangMillsHamiltonianSpectralDerivation3320.lean
MGAP4D/MathlibAnalytic/ContinuumHamiltonianCompleteMassGapDerivation.lean
```

## Positive spectral-mass provenance

The positive/nonzero spectral-mass receipt is:

```text
continuum_hamiltonian_witness_positive_spectral_mass_provenance
```

which points to:

```text
physical_4d_ym_continuum_hamiltonian_complete_spectral_atom_positive_nonzero
```

This is the review target for the claim that the observable spectral mass is positive and nonzero.

## Summary theorem

The whole provenance map is bundled as:

```text
continuum_hamiltonian_witness_provenance_map_ready
```

This theorem is the preferred review entry when an external reader wants to see that the witness slots are not merely carried as opaque receipts, but are connected to named upstream theorem anchors.

## Boundary

This provenance map is still an internal Lean theorem-witness map. It improves mathematical auditability by exposing theorem origins for receipt slots. It does not by itself replace independent mathematical review of the underlying analytic constructions, spectral theorem route, or continuum Yang--Mills interpretation.
