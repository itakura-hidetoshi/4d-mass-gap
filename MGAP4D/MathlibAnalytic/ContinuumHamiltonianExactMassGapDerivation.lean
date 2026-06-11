import MGAP4D.MathlibAnalytic.ContinuumHamiltonianMassGapWitness

namespace MGAP4D
namespace MathlibAnalytic

/--
Continuum Hamiltonian exact mass-gap derivation surface.

This proposition packages the theorem-derived upstream witnesses already carried
by `continuumHamiltonianMassGapWitnessData` into the readable chain from the
physical continuum Yang--Mills lane to a positive exact normalized carrier.  It
intentionally does not prove `exactGapValueReal = (33 : ℝ) / 20` by unfolding the
carrier; a numeric value theorem must enter through the R6 non-definitional
spectral/PVM value-pinning route.
-/
def physicalContinuumHamiltonianToExactPositiveMassGap : Prop :=
  continuumHamiltonianMassGapWitnessData.physicalContinuumHamiltonianReady ∧
  continuumHamiltonianMassGapWitnessData.hphysFromContinuumYMReady ∧
  continuumHamiltonianMassGapWitnessData.selfAdjointSpectralChainReady ∧
  continuumHamiltonianMassGapWitnessData.normalizationToExactGapReady ∧
  0 < exactGapValueReal ∧
  continuumHamiltonianMassGapWitnessData.compactCenteredPlaquetteWeightReady ∧
  continuumHamiltonianMassGapWitnessData.spectralMassObservableReady ∧
  continuumHamiltonianMassGapWitnessData.massGapDerivationWitness ∧
  continuumHamiltonianMassGapWitnessData.publicBoundaryHeld ∧
  continuumHamiltonianMassGapWitnessData.finalReleaseHeld ∧
  finalTheoremReleaseSkeletonReviewSurface.externalConsensusNotClaimed

/-- Physical continuum Yang--Mills Hamiltonian chain yields a positive exact
normalized mass-gap carrier, without adopting the displayed `33/20` value. -/
theorem physical_continuum_hamiltonian_to_exact_positive_mass_gap :
    physicalContinuumHamiltonianToExactPositiveMassGap := by
  unfold physicalContinuumHamiltonianToExactPositiveMassGap
  rcases continuum_hamiltonian_mass_gap_witness_ready with
    ⟨_, _, hPhysical, hHPhys, hSpectral, hNorm, hPos, _,
      hPlaquette, hObservable, hDerivation, _, _, hNoConsensus,
      hPublic, hFinal⟩
  exact And.intro hPhysical <|
    And.intro hHPhys <|
    And.intro hSpectral <|
    And.intro hNorm <|
    And.intro hPos <|
    And.intro hPlaquette <|
    And.intro hObservable <|
    And.intro hDerivation <|
    And.intro hPublic <|
    And.intro hFinal hNoConsensus

/-- Boundary for the exact normalized gap value used by the continuum Hamiltonian
witness.  This is not a numeric `33/20` theorem. -/
def physicalContinuumHamiltonianExactGapValueBoundary : Prop :=
  0 < exactGapValueReal ∧
  continuumHamiltonianMassGapWitnessData.normalizationToExactGapReady ∧
  finalTheoremReleaseSkeletonReviewSurface.externalConsensusNotClaimed

/-- The normalized exact mass-gap carrier is positive and normalization-ready,
while the displayed numeric value remains non-adopted at this level. -/
theorem physical_continuum_hamiltonian_exact_gap_value_boundary :
    physicalContinuumHamiltonianExactGapValueBoundary := by
  unfold physicalContinuumHamiltonianExactGapValueBoundary
  rcases continuum_hamiltonian_mass_gap_witness_ready with
    ⟨_, _, _, _, _, hNorm, hPos, _, _, _, _, _, _, hNoConsensus, _⟩
  exact And.intro hPos <|
    And.intro hNorm hNoConsensus

/-- The continuum Hamiltonian mass-gap witness is theorem-derived from the
upstream continuum Yang--Mills and plaquette spectral-weight hardening lanes. -/
def continuumHamiltonianMassGapTheoremDerivedWitness : Prop :=
  continuumYangMillsLaneHardeningData.ready ∧
  plaquetteSpectralWeightLaneHardeningData.ready ∧
  continuumHamiltonianMassGapWitnessData.ready

/-- No naked witness-only surface is needed at this level: the witness is backed
by upstream hardening-lane ready theorems. -/
theorem continuum_hamiltonian_mass_gap_theorem_derived_witness :
    continuumHamiltonianMassGapTheoremDerivedWitness := by
  unfold continuumHamiltonianMassGapTheoremDerivedWitness
  exact And.intro continuum_yang_mills_lane_hardening_ready <|
    And.intro plaquette_spectral_weight_lane_hardening_ready
      continuum_hamiltonian_mass_gap_witness_ready

end MathlibAnalytic
end MGAP4D
