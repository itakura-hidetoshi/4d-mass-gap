import MGAP4D.MathlibAnalytic.YangMillsHamiltonianSpectralDerivation3320

namespace MGAP4D
namespace R6
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

structure ExactAtom3320YangMillsSpectralDerivation where
  upstreamReady : MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.ready
  spectralInfimum_eq_derived :
    MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.spectralInfimumValue =
      MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue
  attainedSpectralValue_eq_derived :
    MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.attainedSpectralValue =
      MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue
  observableSpectralAtomValue_eq_derived :
    MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.observableSpectralAtomValue =
      MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue
  exactGapCarrier_eq_derived :
    MGAP4D.MathlibAnalytic.exactGapValueReal =
      MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue
  positiveSpectralMass : 0 < MGAP4D.MathlibAnalytic.spectralMassRealSurface.mass
  nonzeroSpectralMass : MGAP4D.MathlibAnalytic.spectralMassRealSurface.mass ≠ 0
  theoremWitnessOnly : Prop
  noExternalConsensusClaim :
    MGAP4D.MathlibAnalytic.finalTheoremReleaseSkeletonReviewSurface.externalConsensusNotClaimed
  publicBoundaryHeld : Prop
  finalReleaseHeld : Prop

def ExactAtom3320YangMillsSpectralDerivation.ready
    (D : ExactAtom3320YangMillsSpectralDerivation) : Prop :=
  MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.ready ∧
  MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.spectralInfimumValue =
    MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue ∧
  MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.attainedSpectralValue =
    MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue ∧
  MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.observableSpectralAtomValue =
    MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue ∧
  MGAP4D.MathlibAnalytic.exactGapValueReal =
    MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue ∧
  0 < MGAP4D.MathlibAnalytic.spectralMassRealSurface.mass ∧
  MGAP4D.MathlibAnalytic.spectralMassRealSurface.mass ≠ 0 ∧
  D.theoremWitnessOnly ∧
  MGAP4D.MathlibAnalytic.finalTheoremReleaseSkeletonReviewSurface.externalConsensusNotClaimed ∧
  D.publicBoundaryHeld ∧
  D.finalReleaseHeld

def exactAtom3320YangMillsSpectralDerivation :
    ExactAtom3320YangMillsSpectralDerivation :=
  { upstreamReady := MGAP4D.MathlibAnalytic.yang_mills_hamiltonian_spectral_derivation_3320_ready
    spectralInfimum_eq_derived :=
      MGAP4D.MathlibAnalytic.yang_mills_hamiltonian_spectral_infimum_eq_derived
    attainedSpectralValue_eq_derived :=
      MGAP4D.MathlibAnalytic.yang_mills_hamiltonian_spectral_attainment_eq_derived
    observableSpectralAtomValue_eq_derived :=
      MGAP4D.MathlibAnalytic.yang_mills_hamiltonian_observable_atom_eq_derived
    exactGapCarrier_eq_derived :=
      MGAP4D.MathlibAnalytic.yang_mills_hamiltonian_exact_gap_eq_spectral_value
    positiveSpectralMass :=
      MGAP4D.MathlibAnalytic.yang_mills_hamiltonian_spectral_derivation_positive_mass
    nonzeroSpectralMass :=
      MGAP4D.MathlibAnalytic.yang_mills_hamiltonian_spectral_derivation_nonzero_mass
    theoremWitnessOnly :=
      MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.theoremWitnessOnly
    noExternalConsensusClaim :=
      MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.noExternalConsensusClaim
    publicBoundaryHeld :=
      MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.publicBoundaryHeld
    finalReleaseHeld :=
      MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.finalReleaseHeld }

theorem exact_atom_3320_yang_mills_spectral_derivation_ready :
    exactAtom3320YangMillsSpectralDerivation.ready := by
  exact ⟨
    exactAtom3320YangMillsSpectralDerivation.upstreamReady,
    exactAtom3320YangMillsSpectralDerivation.spectralInfimum_eq_derived,
    exactAtom3320YangMillsSpectralDerivation.attainedSpectralValue_eq_derived,
    exactAtom3320YangMillsSpectralDerivation.observableSpectralAtomValue_eq_derived,
    exactAtom3320YangMillsSpectralDerivation.exactGapCarrier_eq_derived,
    exactAtom3320YangMillsSpectralDerivation.positiveSpectralMass,
    exactAtom3320YangMillsSpectralDerivation.nonzeroSpectralMass,
    exactAtom3320YangMillsSpectralDerivation.theoremWitnessOnly,
    exactAtom3320YangMillsSpectralDerivation.noExternalConsensusClaim,
    exactAtom3320YangMillsSpectralDerivation.publicBoundaryHeld,
    exactAtom3320YangMillsSpectralDerivation.finalReleaseHeld⟩

theorem exact_atom_3320_yang_mills_exact_gap_carrier_eq_derived :
    MGAP4D.MathlibAnalytic.exactGapValueReal =
      MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue := by
  exact exactAtom3320YangMillsSpectralDerivation.exactGapCarrier_eq_derived

theorem exact_atom_3320_yang_mills_positive_nonzero_spectral_mass :
    0 < MGAP4D.MathlibAnalytic.spectralMassRealSurface.mass ∧
      MGAP4D.MathlibAnalytic.spectralMassRealSurface.mass ≠ 0 := by
  exact ⟨
    exactAtom3320YangMillsSpectralDerivation.positiveSpectralMass,
    exactAtom3320YangMillsSpectralDerivation.nonzeroSpectralMass⟩

def ExactAtom3320YangMillsSpectralValueNonAdoptionAtR6 : Prop :=
  exactAtom3320YangMillsSpectralDerivation.ready ∧
  MGAP4D.MathlibAnalytic.exactGapValueReal =
    MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue ∧
  MGAP4D.MathlibAnalytic.finalTheoremReleaseSkeletonReviewSurface.externalConsensusNotClaimed

theorem exact_atom_3320_yang_mills_spectral_value_nonadoption_at_r6_ready :
    ExactAtom3320YangMillsSpectralValueNonAdoptionAtR6 := by
  exact ⟨
    exact_atom_3320_yang_mills_spectral_derivation_ready,
    exact_atom_3320_yang_mills_exact_gap_carrier_eq_derived,
    exactAtom3320YangMillsSpectralDerivation.noExternalConsensusClaim⟩

end

end Theorem
end R6
end MGAP4D
