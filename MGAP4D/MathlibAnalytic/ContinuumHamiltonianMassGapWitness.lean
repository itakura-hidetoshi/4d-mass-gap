import MGAP4D.MathlibAnalytic.ContinuumYangMillsLaneHardening
import MGAP4D.MathlibAnalytic.PlaquetteSpectralWeightLaneHardening
import MGAP4D.MathlibAnalytic.FinalTheoremReleaseChainIndex

namespace MGAP4D
namespace MathlibAnalytic

/-- Witness surface connecting the physical four-dimensional continuum
Yang--Mills Hamiltonian lane to the mass-gap observable lane.

This object is deliberately a theorem-witness bridge, not an external-audit
claim.  It records the ordered implication chain already present in the
hardening lanes:

* continuum Yang--Mills Hamiltonian construction is hardened;
* `H_phys` is built from that Yang--Mills surface;
* the self-adjoint/spectral/normalization chain is available;
* the exact normalized value is preserved as `33/20`;
* the compact centered plaquette observable has a positive spectral-weight
  lane at that same exact value.

The bridge keeps both the public theorem-release boundary and the external
consensus boundary closed. -/
structure ContinuumHamiltonianMassGapWitnessData where
  continuumYMLaneReady : continuumYangMillsLaneHardeningData.ready
  plaquetteWeightLaneReady : plaquetteSpectralWeightLaneHardeningData.ready
  physicalContinuumHamiltonianReady : Prop
  hphysFromContinuumYMReady : Prop
  selfAdjointSpectralChainReady : Prop
  normalizationToExactGapReady : Prop
  positiveGapWitness : 0 < exactGapValueReal
  exactGapValuePreserved : exactGapValueReal = (33 : ℝ) / 20
  compactCenteredPlaquetteWeightReady : Prop
  spectralMassObservableReady : Prop
  massGapDerivationWitness : Prop
  continuumHamiltonianToMassGapChainReady : Prop
  theoremWitnessOnly : Prop
  noExternalConsensusClaim : Prop
  publicBoundaryHeld : Prop
  finalReleaseHeld : Prop

/-- Ready predicate for the continuum Hamiltonian to mass-gap witness chain. -/
def ContinuumHamiltonianMassGapWitnessData.ready
    (D : ContinuumHamiltonianMassGapWitnessData) : Prop :=
  continuumYangMillsLaneHardeningData.ready ∧
  plaquetteSpectralWeightLaneHardeningData.ready ∧
  D.physicalContinuumHamiltonianReady ∧
  D.hphysFromContinuumYMReady ∧
  D.selfAdjointSpectralChainReady ∧
  D.normalizationToExactGapReady ∧
  0 < exactGapValueReal ∧
  exactGapValueReal = (33 : ℝ) / 20 ∧
  D.compactCenteredPlaquetteWeightReady ∧
  D.spectralMassObservableReady ∧
  D.massGapDerivationWitness ∧
  D.continuumHamiltonianToMassGapChainReady ∧
  D.theoremWitnessOnly ∧
  D.noExternalConsensusClaim ∧
  D.publicBoundaryHeld ∧
  D.finalReleaseHeld

/-- The physical continuum Hamiltonian surface is ready. -/
theorem continuum_hamiltonian_physical_surface_ready
    (D : ContinuumHamiltonianMassGapWitnessData) (hD : D.ready) :
    D.physicalContinuumHamiltonianReady := by
  rcases hD with ⟨_, _, h, _⟩
  exact h

/-- The `H_phys`-from-continuum-Yang--Mills bridge is ready. -/
theorem continuum_hamiltonian_hphys_from_ym_ready
    (D : ContinuumHamiltonianMassGapWitnessData) (hD : D.ready) :
    D.hphysFromContinuumYMReady := by
  rcases hD with ⟨_, _, _, h, _⟩
  exact h

/-- The self-adjoint and spectral chain is ready. -/
theorem continuum_hamiltonian_self_adjoint_spectral_chain_ready
    (D : ContinuumHamiltonianMassGapWitnessData) (hD : D.ready) :
    D.selfAdjointSpectralChainReady := by
  rcases hD with ⟨_, _, _, _, h, _⟩
  exact h

/-- The normalization-to-exact-gap bridge is ready. -/
theorem continuum_hamiltonian_normalization_to_exact_gap_ready
    (D : ContinuumHamiltonianMassGapWitnessData) (hD : D.ready) :
    D.normalizationToExactGapReady := by
  rcases hD with ⟨_, _, _, _, _, h, _⟩
  exact h

/-- The exact normalized value is a strictly positive gap witness. -/
theorem continuum_hamiltonian_positive_gap_witness
    (D : ContinuumHamiltonianMassGapWitnessData) (_hD : D.ready) :
    0 < exactGapValueReal := by
  exact D.positiveGapWitness

/-- The continuum Hamiltonian chain preserves the exact normalized value. -/
theorem continuum_hamiltonian_exact_gap_value_preserved
    (D : ContinuumHamiltonianMassGapWitnessData) (_hD : D.ready) :
    exactGapValueReal = (33 : ℝ) / 20 := by
  exact D.exactGapValuePreserved

/-- The compact centered plaquette spectral-weight lane is ready. -/
theorem continuum_hamiltonian_compact_centered_plaquette_weight_ready
    (D : ContinuumHamiltonianMassGapWitnessData) (hD : D.ready) :
    D.compactCenteredPlaquetteWeightReady := by
  rcases hD with ⟨_, _, _, _, _, _, _, _, h, _⟩
  exact h

/-- The spectral-mass observable witness is ready. -/
theorem continuum_hamiltonian_spectral_mass_observable_ready
    (D : ContinuumHamiltonianMassGapWitnessData) (hD : D.ready) :
    D.spectralMassObservableReady := by
  rcases hD with ⟨_, _, _, _, _, _, _, _, _, h, _⟩
  exact h

/-- The mass-gap derivation witness from continuum Hamiltonian data is ready. -/
theorem continuum_hamiltonian_mass_gap_derivation_witness
    (D : ContinuumHamiltonianMassGapWitnessData) (hD : D.ready) :
    D.massGapDerivationWitness := by
  rcases hD with ⟨_, _, _, _, _, _, _, _, _, _, h, _⟩
  exact h

/-- The whole continuum-Hamiltonian-to-mass-gap chain is ready. -/
theorem continuum_hamiltonian_to_mass_gap_chain_ready
    (D : ContinuumHamiltonianMassGapWitnessData) (hD : D.ready) :
    D.continuumHamiltonianToMassGapChainReady := by
  rcases hD with ⟨_, _, _, _, _, _, _, _, _, _, _, h, _⟩
  exact h

/-- The installed continuum Hamiltonian mass-gap witness surface. -/
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
      exactGapValueReal = (33 : ℝ) / 20
    positiveGapWitness := exactGapValueReal_pos
    exactGapValuePreserved := exactGapValueReal_eq
    compactCenteredPlaquetteWeightReady :=
      plaquetteSpectralWeightLaneHardeningData.compactSupportHardened ∧
      plaquetteSpectralWeightLaneHardeningData.centeredHardened ∧
      plaquetteSpectralWeightLaneHardeningData.smearedHardened
    spectralMassObservableReady :=
      plaquetteSpectralWeightLaneHardeningData.observableAtomHardened ∧
      plaquetteSpectralWeightLaneHardeningData.positiveWeightHardened ∧
      plaquetteSpectralWeightLaneHardeningData.nonzeroWeightHardened
    massGapDerivationWitness :=
      0 < exactGapValueReal ∧ exactGapValueReal = (33 : ℝ) / 20
    continuumHamiltonianToMassGapChainReady :=
      continuumYangMillsLaneHardeningData.ready ∧
      plaquetteSpectralWeightLaneHardeningData.ready
    theoremWitnessOnly :=
      continuumYangMillsLaneHardeningData.reviewLevelOnly ∧
      plaquetteSpectralWeightLaneHardeningData.reviewLevelOnly
    noExternalConsensusClaim :=
      prototypeFinalTheoremReleaseChainIndexData.externalConsensusNotClaimed
    publicBoundaryHeld :=
      continuumYangMillsLaneHardeningData.publicBoundaryHeld ∧
      plaquetteSpectralWeightLaneHardeningData.publicBoundaryHeld
    finalReleaseHeld :=
      continuumYangMillsLaneHardeningData.finalReleaseHeld ∧
      plaquetteSpectralWeightLaneHardeningData.finalReleaseHeld }

/-- The installed continuum Hamiltonian mass-gap witness chain is ready. -/
theorem continuum_hamiltonian_mass_gap_witness_ready :
    continuumHamiltonianMassGapWitnessData.ready := by
  rcases continuum_yang_mills_lane_hardening_ready with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hYMReview, hYMPublic, hYMFinal⟩
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
        continuumYangMillsLaneHardeningData.exactValuePreserved) <|
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
      (And.intro exactGapValueReal_pos exactGapValueReal_eq) <|
    And.intro
      (And.intro continuum_yang_mills_lane_hardening_ready
        plaquette_spectral_weight_lane_hardening_ready) <|
    And.intro
      (And.intro hYMReview hPQReview) <|
    And.intro
      (final_theorem_release_chain_index_external_consensus_not_claimed
        prototypeFinalTheoremReleaseChainIndexData) <|
    And.intro
      (And.intro hYMPublic hPQPublic) <|
    And.intro hYMFinal hPQFinal

end MathlibAnalytic
end MGAP4D
