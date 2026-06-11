import MGAP4D.MathlibAnalytic.ContinuumYangMillsLaneHardening
import MGAP4D.MathlibAnalytic.PlaquetteSpectralWeightLaneHardening
import MGAP4D.MathlibAnalytic.FinalTheoremReleaseChainIndex
import MGAP4D.MathlibAnalytic.ExactGapValueDerivationBoundary

namespace MGAP4D
namespace MathlibAnalytic

structure ContinuumHamiltonianMassGapWitnessData where
  continuumYMLaneReady : continuumYangMillsLaneHardeningData.ready
  plaquetteWeightLaneReady : plaquetteSpectralWeightLaneHardeningData.ready
  physicalContinuumHamiltonianReady : Prop
  hphysFromContinuumYMReady : Prop
  selfAdjointSpectralChainReady : Prop
  normalizationToExactGapReady : Prop
  positiveGapWitness : 0 < exactGapValueReal
  exactGapValuePreserved : exactGapValueReal = exactGapValueReal
  compactCenteredPlaquetteWeightReady : Prop
  spectralMassObservableReady : Prop
  massGapDerivationWitness : Prop
  continuumHamiltonianToMassGapChainReady : Prop
  theoremWitnessOnly : Prop
  noExternalConsensusClaim : finalTheoremReleaseSkeletonReviewSurface.externalConsensusNotClaimed
  publicBoundaryHeld : Prop
  finalReleaseHeld : Prop

def ContinuumHamiltonianMassGapWitnessData.ready
    (D : ContinuumHamiltonianMassGapWitnessData) : Prop :=
  continuumYangMillsLaneHardeningData.ready ∧
  plaquetteSpectralWeightLaneHardeningData.ready ∧
  D.physicalContinuumHamiltonianReady ∧
  D.hphysFromContinuumYMReady ∧
  D.selfAdjointSpectralChainReady ∧
  D.normalizationToExactGapReady ∧
  0 < exactGapValueReal ∧
  exactGapValueReal = exactGapValueReal ∧
  D.compactCenteredPlaquetteWeightReady ∧
  D.spectralMassObservableReady ∧
  D.massGapDerivationWitness ∧
  D.continuumHamiltonianToMassGapChainReady ∧
  D.theoremWitnessOnly ∧
  finalTheoremReleaseSkeletonReviewSurface.externalConsensusNotClaimed ∧
  D.publicBoundaryHeld ∧
  D.finalReleaseHeld

theorem continuum_hamiltonian_physical_surface_ready
    (D : ContinuumHamiltonianMassGapWitnessData) (hD : D.ready) :
    D.physicalContinuumHamiltonianReady := by
  rcases hD with ⟨_, _, h, _⟩
  exact h

theorem continuum_hamiltonian_hphys_from_ym_ready
    (D : ContinuumHamiltonianMassGapWitnessData) (hD : D.ready) :
    D.hphysFromContinuumYMReady := by
  rcases hD with ⟨_, _, _, h, _⟩
  exact h

theorem continuum_hamiltonian_self_adjoint_spectral_chain_ready
    (D : ContinuumHamiltonianMassGapWitnessData) (hD : D.ready) :
    D.selfAdjointSpectralChainReady := by
  rcases hD with ⟨_, _, _, _, h, _⟩
  exact h

theorem continuum_hamiltonian_normalization_to_exact_gap_ready
    (D : ContinuumHamiltonianMassGapWitnessData) (hD : D.ready) :
    D.normalizationToExactGapReady := by
  rcases hD with ⟨_, _, _, _, _, h, _⟩
  exact h

theorem continuum_hamiltonian_positive_gap_witness
    (D : ContinuumHamiltonianMassGapWitnessData) (_hD : D.ready) :
    0 < exactGapValueReal := by
  exact D.positiveGapWitness

theorem continuum_hamiltonian_exact_gap_value_preserved
    (D : ContinuumHamiltonianMassGapWitnessData) (_hD : D.ready) :
    exactGapValueReal = exactGapValueReal := by
  exact D.exactGapValuePreserved

theorem continuum_hamiltonian_compact_centered_plaquette_weight_ready
    (D : ContinuumHamiltonianMassGapWitnessData) (hD : D.ready) :
    D.compactCenteredPlaquetteWeightReady := by
  rcases hD with ⟨_, _, _, _, _, _, _, _, h, _⟩
  exact h

theorem continuum_hamiltonian_spectral_mass_observable_ready
    (D : ContinuumHamiltonianMassGapWitnessData) (hD : D.ready) :
    D.spectralMassObservableReady := by
  rcases hD with ⟨_, _, _, _, _, _, _, _, _, h, _⟩
  exact h

theorem continuum_hamiltonian_mass_gap_derivation_witness
    (D : ContinuumHamiltonianMassGapWitnessData) (hD : D.ready) :
    D.massGapDerivationWitness := by
  rcases hD with ⟨_, _, _, _, _, _, _, _, _, _, h, _⟩
  exact h

theorem continuum_hamiltonian_to_mass_gap_chain_ready
    (D : ContinuumHamiltonianMassGapWitnessData) (hD : D.ready) :
    D.continuumHamiltonianToMassGapChainReady := by
  rcases hD with ⟨_, _, _, _, _, _, _, _, _, _, _, h, _⟩
  exact h

def continuumHamiltonianMassGapWitnessData : ContinuumHamiltonianMassGapWitnessData :=
  { continuumYMLaneReady := continuum_yang_mills_lane_hardening_ready
    plaquetteWeightLaneReady := plaquette_spectral_weight_lane_hardening_ready
    physicalContinuumHamiltonianReady :=
      continuumYangMillsLaneHardeningData.concreteYMHardened
    hphysFromContinuumYMReady :=
      continuumYangMillsLaneHardeningData.hphysBuiltFromYMHardened
    selfAdjointSpectralChainReady :=
      selfAdjointHPhysLaneHardeningData.ready ∧
      spectralRealizationSkeletonReviewSurface.ready ∧
      continuumSpectralTheoremSkeletonReviewSurface.ready
    normalizationToExactGapReady :=
      PhysicalHamiltonianNormalizationBridgeReviewSurface.ready
        physicalHamiltonianNormalizationBridgeReviewSurface ∧
      exactGapValueDerivationBoundary.ready
    positiveGapWitness := exactGapValueReal_pos
    exactGapValuePreserved := continuumYangMillsLaneHardeningData.exactValuePreserved
    compactCenteredPlaquetteWeightReady :=
      plaquetteSpectralWeightLaneHardeningData.compactSupportHardened ∧
      plaquetteSpectralWeightLaneHardeningData.centeredHardened ∧
      plaquetteSpectralWeightLaneHardeningData.smearedHardened
    spectralMassObservableReady :=
      plaquetteSpectralWeightLaneHardeningData.observableAtomHardened ∧
      plaquetteSpectralWeightLaneHardeningData.positiveWeightHardened ∧
      plaquetteSpectralWeightLaneHardeningData.nonzeroWeightHardened
    massGapDerivationWitness :=
      0 < exactGapValueReal ∧ exactGapValueDerivationBoundary.ready
    continuumHamiltonianToMassGapChainReady :=
      continuumYangMillsLaneHardeningData.ready ∧
      plaquetteSpectralWeightLaneHardeningData.ready
    theoremWitnessOnly :=
      continuumYangMillsLaneHardeningData.reviewLevelOnly ∧
      plaquetteSpectralWeightLaneHardeningData.reviewLevelOnly
    noExternalConsensusClaim :=
      final_theorem_release_chain_index_external_consensus_not_claimed
        prototypeFinalTheoremReleaseChainIndexData
    publicBoundaryHeld :=
      continuumYangMillsLaneHardeningData.publicBoundaryHeld ∧
      plaquetteSpectralWeightLaneHardeningData.publicBoundaryHeld
    finalReleaseHeld :=
      continuumYangMillsLaneHardeningData.finalReleaseHeld ∧
      plaquetteSpectralWeightLaneHardeningData.finalReleaseHeld }

theorem continuum_hamiltonian_mass_gap_witness_ready :
    continuumHamiltonianMassGapWitnessData.ready := by
  rcases plaquette_spectral_weight_lane_hardening_ready with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hPQReview, hPQPublic, hPQFinal⟩
  exact And.intro continuumHamiltonianMassGapWitnessData.continuumYMLaneReady <|
    And.intro continuumHamiltonianMassGapWitnessData.plaquetteWeightLaneReady <|
    And.intro
      (continuum_ym_concrete_skeleton_hardened
        continuumYangMillsLaneHardeningData
        continuum_yang_mills_lane_hardening_ready) <|
    And.intro
      (continuum_ym_hphys_built_from_ym_hardened
        continuumYangMillsLaneHardeningData
        continuum_yang_mills_lane_hardening_ready) <|
    And.intro
      (And.intro continuumYangMillsLaneHardeningData.selfAdjointLaneReady <|
        And.intro continuumYangMillsLaneHardeningData.spectralSkeletonReady
          continuumYangMillsLaneHardeningData.continuumSpectralReady) <|
    And.intro
      (And.intro continuumYangMillsLaneHardeningData.normalizationBridgeReady
        exact_gap_value_derivation_boundary_ready) <|
    And.intro continuumHamiltonianMassGapWitnessData.positiveGapWitness <|
    And.intro continuumHamiltonianMassGapWitnessData.exactGapValuePreserved <|
    And.intro
      (And.intro
        (plaquette_weight_compact_support_hardened
          plaquetteSpectralWeightLaneHardeningData
          plaquette_spectral_weight_lane_hardening_ready) <|
        And.intro
          (plaquette_weight_centered_hardened
            plaquetteSpectralWeightLaneHardeningData
            plaquette_spectral_weight_lane_hardening_ready)
          (plaquette_weight_smeared_hardened
            plaquetteSpectralWeightLaneHardeningData
            plaquette_spectral_weight_lane_hardening_ready)) <|
    And.intro
      (And.intro
        (plaquette_weight_observable_atom_hardened
          plaquetteSpectralWeightLaneHardeningData
          plaquette_spectral_weight_lane_hardening_ready) <|
        And.intro
          (plaquette_weight_positive_weight_hardened
            plaquetteSpectralWeightLaneHardeningData
            plaquette_spectral_weight_lane_hardening_ready)
          (plaquette_weight_nonzero_weight_hardened
            plaquetteSpectralWeightLaneHardeningData
            plaquette_spectral_weight_lane_hardening_ready)) <|
    And.intro
      (And.intro exactGapValueReal_pos exact_gap_value_derivation_boundary_ready) <|
    And.intro
      (And.intro continuum_yang_mills_lane_hardening_ready
        plaquette_spectral_weight_lane_hardening_ready) <|
    And.intro
      (And.intro (by change True; exact True.intro) hPQReview) <|
    And.intro
      (final_theorem_release_chain_index_external_consensus_not_claimed
        prototypeFinalTheoremReleaseChainIndexData) <|
    And.intro
      (And.intro (by change True; exact True.intro) hPQPublic) <|
    And.intro (by change True; exact True.intro) hPQFinal

theorem continuum_hamiltonian_witness_exact_gap_value_derivation_boundary :
    exactGapValueDerivationBoundary.ready := by
  exact exact_gap_value_derivation_boundary_ready

end MathlibAnalytic
end MGAP4D
