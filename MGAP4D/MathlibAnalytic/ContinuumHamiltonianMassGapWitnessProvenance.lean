import MGAP4D.MathlibAnalytic.ContinuumHamiltonianCompleteMassGapDerivation

namespace MGAP4D
namespace MathlibAnalytic

/-- Provenance map for the physical-continuum-Hamiltonian slot.

This theorem intentionally exposes the concrete upstream theorem that generates
`physicalContinuumHamiltonianReady`, rather than treating that slot as an opaque
receipt. -/
theorem continuum_hamiltonian_witness_physical_surface_provenance :
    continuumHamiltonianMassGapWitnessData.physicalContinuumHamiltonianReady := by
  exact continuum_ym_concrete_skeleton_hardened
    continuumYangMillsLaneHardeningData
    continuum_yang_mills_lane_hardening_ready

/-- Provenance map for the `H_phys`-from-Yang--Mills slot. -/
theorem continuum_hamiltonian_witness_hphys_from_ym_provenance :
    continuumHamiltonianMassGapWitnessData.hphysFromContinuumYMReady := by
  exact continuum_ym_hphys_built_from_ym_hardened
    continuumYangMillsLaneHardeningData
    continuum_yang_mills_lane_hardening_ready

/-- Provenance map for the self-adjoint / spectral chain slot. -/
theorem continuum_hamiltonian_witness_self_adjoint_spectral_source_provenance :
    selfAdjointHPhysLaneHardeningData.ready ∧
      spectralRealizationSkeletonReviewSurface.ready ∧
      continuumSpectralTheoremSkeletonReviewSurface.ready := by
  exact And.intro self_adjoint_hphys_lane_hardening_ready <|
    And.intro spectral_realization_skeleton_review_surface_ready
      continuum_spectral_theorem_skeleton_review_surface_ready

/-- Slot-level projection of the self-adjoint / spectral provenance. -/
theorem continuum_hamiltonian_witness_self_adjoint_spectral_slot_provenance :
    continuumHamiltonianMassGapWitnessData.selfAdjointSpectralChainReady := by
  exact continuum_hamiltonian_witness_self_adjoint_spectral_source_provenance

/-- Provenance map for the exact-value derivation receipt.

The exact value is read here through the spectral derivation route, not merely
through the carrier equality in `ExactGapReal.lean`. -/
theorem continuum_hamiltonian_witness_exact_value_derivation_provenance :
    exactGapValueReal = (33 : ℝ) / 20 := by
  exact physical_4d_ym_continuum_hamiltonian_complete_spectral_derivation_exact_gap

/-- Provenance map for the normalization-to-exact-gap slot.

The normalization slot now consumes the concrete spectral derivation theorem
rather than the carrier-level closed-form equality. -/
theorem continuum_hamiltonian_witness_normalization_source_provenance :
    PhysicalHamiltonianNormalizationBridgeReviewSurface.ready
        physicalHamiltonianNormalizationBridgeReviewSurface ∧
      exactGapValueReal = (33 : ℝ) / 20 := by
  exact And.intro physical_hamiltonian_normalization_bridge_review_surface_ready
    continuum_hamiltonian_witness_exact_value_derivation_provenance

/-- Slot-level projection of the normalization provenance. -/
theorem continuum_hamiltonian_witness_normalization_slot_provenance :
    continuumHamiltonianMassGapWitnessData.normalizationToExactGapReady := by
  exact continuum_hamiltonian_witness_normalization_source_provenance

/-- Provenance map for the compact-centered-plaquette observable route. -/
theorem continuum_hamiltonian_witness_compact_plaquette_provenance :
    continuumHamiltonianMassGapWitnessData.compactCenteredPlaquetteWeightReady := by
  exact And.intro
    (plaquette_weight_compact_support_hardened
      plaquetteSpectralWeightLaneHardeningData
      plaquette_spectral_weight_lane_hardening_ready) <|
    And.intro
      (plaquette_weight_centered_hardened
        plaquetteSpectralWeightLaneHardeningData
        plaquette_spectral_weight_lane_hardening_ready)
      (plaquette_weight_smeared_hardened
        plaquetteSpectralWeightLaneHardeningData
        plaquette_spectral_weight_lane_hardening_ready)

/-- Provenance map for the observable spectral-mass route. -/
theorem continuum_hamiltonian_witness_spectral_mass_observable_provenance :
    continuumHamiltonianMassGapWitnessData.spectralMassObservableReady := by
  exact And.intro
    (plaquette_weight_observable_atom_hardened
      plaquetteSpectralWeightLaneHardeningData
      plaquette_spectral_weight_lane_hardening_ready) <|
    And.intro
      (plaquette_weight_positive_weight_hardened
        plaquetteSpectralWeightLaneHardeningData
        plaquette_spectral_weight_lane_hardening_ready)
      (plaquette_weight_nonzero_weight_hardened
        plaquetteSpectralWeightLaneHardeningData
        plaquette_spectral_weight_lane_hardening_ready)

/-- Provenance map for the positive/nonzero observable spectral mass. -/
theorem continuum_hamiltonian_witness_positive_spectral_mass_provenance :
    0 < spectralMassRealSurface.mass ∧ spectralMassRealSurface.mass ≠ 0 := by
  exact physical_4d_ym_continuum_hamiltonian_complete_spectral_atom_positive_nonzero

/-- Slot-level provenance for the mass-gap derivation witness.

This keeps the old witness slot compatible with the newer spectral derivation
route by pairing the installed positivity theorem with the complete spectral
exact-value derivation. -/
theorem continuum_hamiltonian_witness_mass_gap_derivation_slot_provenance :
    continuumHamiltonianMassGapWitnessData.massGapDerivationWitness := by
  exact And.intro continuum_hamiltonian_derives_positive_mass_gap
    continuum_hamiltonian_witness_exact_value_derivation_provenance

/-- Provenance map for the whole continuum-Hamiltonian-to-mass-gap chain slot. -/
theorem continuum_hamiltonian_witness_chain_slot_provenance :
    continuumHamiltonianMassGapWitnessData.continuumHamiltonianToMassGapChainReady := by
  exact And.intro continuum_yang_mills_lane_hardening_ready
    plaquette_spectral_weight_lane_hardening_ready

/-- External-review summary: every non-boundary `ContinuumHamiltonianMassGapWitnessData`
slot is now paired with an explicit upstream theorem anchor. -/
theorem continuum_hamiltonian_witness_provenance_map_ready :
    continuumHamiltonianMassGapWitnessData.physicalContinuumHamiltonianReady ∧
      continuumHamiltonianMassGapWitnessData.hphysFromContinuumYMReady ∧
      continuumHamiltonianMassGapWitnessData.selfAdjointSpectralChainReady ∧
      continuumHamiltonianMassGapWitnessData.normalizationToExactGapReady ∧
      continuumHamiltonianMassGapWitnessData.compactCenteredPlaquetteWeightReady ∧
      continuumHamiltonianMassGapWitnessData.spectralMassObservableReady ∧
      continuumHamiltonianMassGapWitnessData.massGapDerivationWitness ∧
      continuumHamiltonianMassGapWitnessData.continuumHamiltonianToMassGapChainReady ∧
      exactGapValueReal = (33 : ℝ) / 20 ∧
      0 < spectralMassRealSurface.mass ∧
      spectralMassRealSurface.mass ≠ 0 := by
  exact And.intro continuum_hamiltonian_witness_physical_surface_provenance <|
    And.intro continuum_hamiltonian_witness_hphys_from_ym_provenance <|
    And.intro continuum_hamiltonian_witness_self_adjoint_spectral_slot_provenance <|
    And.intro continuum_hamiltonian_witness_normalization_slot_provenance <|
    And.intro continuum_hamiltonian_witness_compact_plaquette_provenance <|
    And.intro continuum_hamiltonian_witness_spectral_mass_observable_provenance <|
    And.intro continuum_hamiltonian_witness_mass_gap_derivation_slot_provenance <|
    And.intro continuum_hamiltonian_witness_chain_slot_provenance <|
    And.intro continuum_hamiltonian_witness_exact_value_derivation_provenance
      continuum_hamiltonian_witness_positive_spectral_mass_provenance

end MathlibAnalytic
end MGAP4D
