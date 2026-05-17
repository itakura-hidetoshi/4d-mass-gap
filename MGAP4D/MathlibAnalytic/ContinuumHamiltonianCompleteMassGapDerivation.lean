import MGAP4D.MathlibAnalytic.ContinuumHamiltonianMassGapReleaseAdoption

namespace MGAP4D
namespace MathlibAnalytic

/-- Complete additive derivation surface from the physical four-dimensional
continuum Yang--Mills Hamiltonian lane to the exact positive mass-gap theorem.

This theorem is intentionally an internal Lean witness surface.  It does not
claim external mathematical consensus; it states that the currently installed
review-level Hamiltonian, spectral/PVM, observable-weight, and release-boundary
surfaces compose to the exact normalized value `33/20` with a positive gap. -/
theorem physical_4d_ym_continuum_hamiltonian_derives_complete_exact_mass_gap :
    continuumYangMillsLaneHardeningData.ready ∧
      plaquetteSpectralWeightLaneHardeningData.ready ∧
      continuumHamiltonianMassGapWitnessData.ready ∧
      continuumHamiltonianMassGapWitnessData.physicalContinuumHamiltonianReady ∧
      continuumHamiltonianMassGapWitnessData.hphysFromContinuumYMReady ∧
      continuumHamiltonianMassGapWitnessData.selfAdjointSpectralChainReady ∧
      continuumHamiltonianMassGapWitnessData.normalizationToExactGapReady ∧
      continuumHamiltonianMassGapWitnessData.compactCenteredPlaquetteWeightReady ∧
      continuumHamiltonianMassGapWitnessData.spectralMassObservableReady ∧
      0 < exactGapValueReal ∧
      exactGapValueReal = (33 : ℝ) / 20 ∧
      continuumHamiltonianMassGapWitnessData.massGapDerivationWitness ∧
      continuumHamiltonianMassGapWitnessData.continuumHamiltonianToMassGapChainReady ∧
      continuumHamiltonianMassGapWitnessData.theoremWitnessOnly ∧
      continuumHamiltonianMassGapWitnessData.noExternalConsensusClaim ∧
      continuumHamiltonianMassGapWitnessData.publicBoundaryHeld ∧
      continuumHamiltonianMassGapWitnessData.finalReleaseHeld := by
  rcases continuum_hamiltonian_mass_gap_witness_ready with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, hWitnessOnly, hNoConsensus, hPublic, hFinal⟩
  exact And.intro continuum_yang_mills_lane_hardening_ready <|
    And.intro plaquette_spectral_weight_lane_hardening_ready <|
    And.intro continuum_hamiltonian_mass_gap_witness_ready <|
    And.intro
      (continuum_hamiltonian_physical_surface_ready
        continuumHamiltonianMassGapWitnessData
        continuum_hamiltonian_mass_gap_witness_ready) <|
    And.intro
      (continuum_hamiltonian_hphys_from_ym_ready
        continuumHamiltonianMassGapWitnessData
        continuum_hamiltonian_mass_gap_witness_ready) <|
    And.intro
      (continuum_hamiltonian_self_adjoint_spectral_chain_ready
        continuumHamiltonianMassGapWitnessData
        continuum_hamiltonian_mass_gap_witness_ready) <|
    And.intro
      (continuum_hamiltonian_normalization_to_exact_gap_ready
        continuumHamiltonianMassGapWitnessData
        continuum_hamiltonian_mass_gap_witness_ready) <|
    And.intro
      (continuum_hamiltonian_compact_centered_plaquette_weight_ready
        continuumHamiltonianMassGapWitnessData
        continuum_hamiltonian_mass_gap_witness_ready) <|
    And.intro
      (continuum_hamiltonian_spectral_mass_observable_ready
        continuumHamiltonianMassGapWitnessData
        continuum_hamiltonian_mass_gap_witness_ready) <|
    And.intro continuum_hamiltonian_derives_positive_mass_gap <|
    And.intro continuum_hamiltonian_derives_exact_mass_gap_value <|
    And.intro
      (continuum_hamiltonian_mass_gap_derivation_witness
        continuumHamiltonianMassGapWitnessData
        continuum_hamiltonian_mass_gap_witness_ready) <|
    And.intro continuum_hamiltonian_derives_mass_gap_chain <|
    And.intro hWitnessOnly <|
    And.intro hNoConsensus <|
    And.intro hPublic hFinal

/-- Public-boundary projection for the complete continuum-Hamiltonian derivation. -/
theorem physical_4d_ym_continuum_hamiltonian_complete_derivation_public_boundary_held :
    continuumHamiltonianMassGapWitnessData.publicBoundaryHeld := by
  rcases physical_4d_ym_continuum_hamiltonian_derives_complete_exact_mass_gap with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hPublic, _⟩
  exact hPublic

/-- Final-release-boundary projection for the complete continuum-Hamiltonian derivation. -/
theorem physical_4d_ym_continuum_hamiltonian_complete_derivation_final_release_held :
    continuumHamiltonianMassGapWitnessData.finalReleaseHeld := by
  rcases physical_4d_ym_continuum_hamiltonian_derives_complete_exact_mass_gap with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hFinal⟩
  exact hFinal

/-- Exact positive gap projection for the complete continuum-Hamiltonian derivation. -/
theorem physical_4d_ym_continuum_hamiltonian_complete_derivation_exact_positive_gap :
    0 < exactGapValueReal ∧ exactGapValueReal = (33 : ℝ) / 20 := by
  rcases physical_4d_ym_continuum_hamiltonian_derives_complete_exact_mass_gap with
    ⟨_, _, _, _, _, _, _, _, _, hPos, hExact, _⟩
  exact And.intro hPos hExact

/-- External-consensus boundary projection for the complete continuum-Hamiltonian derivation. -/
theorem physical_4d_ym_continuum_hamiltonian_complete_derivation_no_external_consensus_claim :
    continuumHamiltonianMassGapWitnessData.noExternalConsensusClaim := by
  rcases physical_4d_ym_continuum_hamiltonian_derives_complete_exact_mass_gap with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hNoConsensus, _⟩
  exact hNoConsensus

end MathlibAnalytic
end MGAP4D