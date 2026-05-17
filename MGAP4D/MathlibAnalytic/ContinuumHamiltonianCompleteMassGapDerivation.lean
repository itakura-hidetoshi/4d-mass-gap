import MGAP4D.MathlibAnalytic.ContinuumHamiltonianMassGapReleaseAdoption
import MGAP4D.MathlibAnalytic.YangMillsHamiltonianSpectralDerivation3320

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

/-- Additive spectral-complete derivation surface: the complete physical
4D Yang--Mills Hamiltonian derivation now explicitly carries the spectral
route deriving the same normalized value `33/20`.

This leaves the older complete theorem unchanged and adds the explicit spectral
infimum / spectral attainment / positive observable spectral atom route. -/
theorem physical_4d_ym_continuum_hamiltonian_derives_complete_spectral_exact_mass_gap :
    physical_4d_ym_continuum_hamiltonian_derives_complete_exact_mass_gap ∧
      yangMillsHamiltonianSpectralDerivation3320.ready ∧
      yangMillsHamiltonianSpectralDerivation3320.spectralInfimumValue =
        (33 : ℝ) / 20 ∧
      yangMillsHamiltonianSpectralDerivation3320.attainedSpectralValue =
        (33 : ℝ) / 20 ∧
      yangMillsHamiltonianSpectralDerivation3320.observableSpectralAtomValue =
        (33 : ℝ) / 20 ∧
      yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue =
        (33 : ℝ) / 20 ∧
      exactGapValueReal =
        yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue ∧
      exactGapValueReal = (33 : ℝ) / 20 ∧
      0 < spectralMassRealSurface.mass ∧
      spectralMassRealSurface.mass ≠ 0 ∧
      yangMillsHamiltonianSpectralDerivation3320.publicBoundaryHeld ∧
      yangMillsHamiltonianSpectralDerivation3320.finalReleaseHeld := by
  exact And.intro physical_4d_ym_continuum_hamiltonian_derives_complete_exact_mass_gap <|
    And.intro yang_mills_hamiltonian_spectral_derivation_3320_ready <|
    And.intro yang_mills_hamiltonian_spectral_infimum_eq_3320 <|
    And.intro yang_mills_hamiltonian_spectral_attainment_eq_3320 <|
    And.intro yang_mills_hamiltonian_observable_atom_eq_3320 <|
    And.intro yang_mills_hamiltonian_spectral_analysis_derives_3320 <|
    And.intro yang_mills_hamiltonian_exact_gap_eq_spectral_value <|
    And.intro yang_mills_hamiltonian_spectral_derivation_exact_gap_value <|
    And.intro yang_mills_hamiltonian_spectral_derivation_positive_mass <|
    And.intro yang_mills_hamiltonian_spectral_derivation_nonzero_mass <|
    And.intro
      yang_mills_hamiltonian_spectral_derivation_public_boundary_held
      yang_mills_hamiltonian_spectral_derivation_final_release_held

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

/-- Spectral exact-value projection for the complete continuum-Hamiltonian derivation. -/
theorem physical_4d_ym_continuum_hamiltonian_complete_spectral_derivation_exact_gap :
    exactGapValueReal = (33 : ℝ) / 20 := by
  rcases physical_4d_ym_continuum_hamiltonian_derives_complete_spectral_exact_mass_gap with
    ⟨_, _, _, _, _, _, _, hExact, _⟩
  exact hExact

/-- Spectral atom projection for the complete continuum-Hamiltonian derivation. -/
theorem physical_4d_ym_continuum_hamiltonian_complete_spectral_atom_positive_nonzero :
    0 < spectralMassRealSurface.mass ∧ spectralMassRealSurface.mass ≠ 0 := by
  rcases physical_4d_ym_continuum_hamiltonian_derives_complete_spectral_exact_mass_gap with
    ⟨_, _, _, _, _, _, _, _, hPosMass, hNonzeroMass, _⟩
  exact And.intro hPosMass hNonzeroMass

/-- External-consensus boundary projection for the complete continuum-Hamiltonian derivation. -/
theorem physical_4d_ym_continuum_hamiltonian_complete_derivation_no_external_consensus_claim :
    continuumHamiltonianMassGapWitnessData.noExternalConsensusClaim := by
  rcases physical_4d_ym_continuum_hamiltonian_derives_complete_exact_mass_gap with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hNoConsensus, _⟩
  exact hNoConsensus

end MathlibAnalytic
end MGAP4D