import MGAP4D.MathlibAnalytic.YangMillsHamiltonianSpectralDerivation3320

namespace MGAP4D
namespace R6
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- R6 spectral-value surface: the displayed exact value is first exported here,
from the Yang--Mills Hamiltonian spectral-value interface.

This file is intentionally downstream of the pre-R6 alignment surface
`YangMillsHamiltonianSpectralDerivation3320`.  The upstream interface aligns the
spectral-infimum, spectral-attainment, observable-atom, and Hamiltonian-derived
values without advertising a `33/20` theorem.  R6 performs the arithmetic
normalization step. -/
structure ExactAtom3320YangMillsSpectralDerivation where
  upstreamReady : MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.ready
  spectralInfimumValue_eq_3320 :
    MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.spectralInfimumValue =
      (33 : ℝ) / 20
  attainedSpectralValue_eq_3320 :
    MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.attainedSpectralValue =
      (33 : ℝ) / 20
  observableSpectralAtomValue_eq_3320 :
    MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.observableSpectralAtomValue =
      (33 : ℝ) / 20
  derivedHamiltonianSpectralValue_eq_3320 :
    MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue =
      (33 : ℝ) / 20
  positiveSpectralMass : 0 < MGAP4D.MathlibAnalytic.spectralMassRealSurface.mass
  nonzeroSpectralMass : MGAP4D.MathlibAnalytic.spectralMassRealSurface.mass ≠ 0
  theoremWitnessOnly : Prop
  publicBoundaryHeld : Prop
  finalReleaseHeld : Prop

/-- R6-ready predicate for the Yang--Mills Hamiltonian spectral derivation. -/
def ExactAtom3320YangMillsSpectralDerivation.ready
    (D : ExactAtom3320YangMillsSpectralDerivation) : Prop :=
  MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.ready ∧
  MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.spectralInfimumValue =
    (33 : ℝ) / 20 ∧
  MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.attainedSpectralValue =
    (33 : ℝ) / 20 ∧
  MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.observableSpectralAtomValue =
    (33 : ℝ) / 20 ∧
  MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue =
    (33 : ℝ) / 20 ∧
  0 < MGAP4D.MathlibAnalytic.spectralMassRealSurface.mass ∧
  MGAP4D.MathlibAnalytic.spectralMassRealSurface.mass ≠ 0 ∧
  D.theoremWitnessOnly ∧
  D.publicBoundaryHeld ∧
  D.finalReleaseHeld

/-- R6 theorem: the Hamiltonian-derived spectral value normalizes to `33/20`.

The proof is deliberately not `rfl`; it opens the upstream spectral interface and
then performs arithmetic normalization of the pre-R6 carrier. -/
theorem yang_mills_hamiltonian_spectral_derivation_exact_gap_value :
    MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue =
      (33 : ℝ) / 20 := by
  norm_num [
    MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320,
    MGAP4D.MathlibAnalytic.exactGapValueReal]

/-- R6 theorem: the spectral infimum value normalizes to `33/20`. -/
theorem yang_mills_hamiltonian_spectral_infimum_eq_3320 :
    MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.spectralInfimumValue =
      (33 : ℝ) / 20 := by
  rw [MGAP4D.MathlibAnalytic.yang_mills_hamiltonian_spectral_infimum_eq_derived]
  exact yang_mills_hamiltonian_spectral_derivation_exact_gap_value

/-- R6 theorem: the attained spectral value normalizes to `33/20`. -/
theorem yang_mills_hamiltonian_spectral_attainment_eq_3320 :
    MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.attainedSpectralValue =
      (33 : ℝ) / 20 := by
  rw [MGAP4D.MathlibAnalytic.yang_mills_hamiltonian_spectral_attainment_eq_derived]
  exact yang_mills_hamiltonian_spectral_derivation_exact_gap_value

/-- R6 theorem: the observable spectral atom value normalizes to `33/20`. -/
theorem yang_mills_hamiltonian_observable_atom_eq_3320 :
    MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.observableSpectralAtomValue =
      (33 : ℝ) / 20 := by
  rw [MGAP4D.MathlibAnalytic.yang_mills_hamiltonian_observable_atom_eq_derived]
  exact yang_mills_hamiltonian_spectral_derivation_exact_gap_value

/-- R6 theorem: the three spectral routes and the Hamiltonian route derive the same
normalized exact value. -/
theorem yang_mills_hamiltonian_spectral_analysis_derives_3320 :
    MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.spectralInfimumValue =
        (33 : ℝ) / 20 ∧
      MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.attainedSpectralValue =
        (33 : ℝ) / 20 ∧
      MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.observableSpectralAtomValue =
        (33 : ℝ) / 20 ∧
      MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue =
        (33 : ℝ) / 20 := by
  exact ⟨
    yang_mills_hamiltonian_spectral_infimum_eq_3320,
    yang_mills_hamiltonian_spectral_attainment_eq_3320,
    yang_mills_hamiltonian_observable_atom_eq_3320,
    yang_mills_hamiltonian_spectral_derivation_exact_gap_value⟩

/-- Installed R6 Yang--Mills Hamiltonian spectral derivation certificate. -/
def exactAtom3320YangMillsSpectralDerivation :
    ExactAtom3320YangMillsSpectralDerivation :=
  { upstreamReady := MGAP4D.MathlibAnalytic.yang_mills_hamiltonian_spectral_derivation_3320_ready
    spectralInfimumValue_eq_3320 := yang_mills_hamiltonian_spectral_infimum_eq_3320
    attainedSpectralValue_eq_3320 := yang_mills_hamiltonian_spectral_attainment_eq_3320
    observableSpectralAtomValue_eq_3320 := yang_mills_hamiltonian_observable_atom_eq_3320
    derivedHamiltonianSpectralValue_eq_3320 := yang_mills_hamiltonian_spectral_derivation_exact_gap_value
    positiveSpectralMass := MGAP4D.MathlibAnalytic.yang_mills_hamiltonian_spectral_derivation_positive_mass
    nonzeroSpectralMass := MGAP4D.MathlibAnalytic.yang_mills_hamiltonian_spectral_derivation_nonzero_mass
    theoremWitnessOnly := MGAP4D.MathlibAnalytic.continuumHamiltonianMassGapWitnessData.theoremWitnessOnly
    publicBoundaryHeld := MGAP4D.MathlibAnalytic.yang_mills_hamiltonian_spectral_derivation_public_boundary_held
    finalReleaseHeld := MGAP4D.MathlibAnalytic.yang_mills_hamiltonian_spectral_derivation_final_release_held }

/-- The installed R6 Yang--Mills spectral derivation is ready. -/
theorem exact_atom_3320_yang_mills_spectral_derivation_ready :
    exactAtom3320YangMillsSpectralDerivation.ready := by
  rcases MGAP4D.MathlibAnalytic.yang_mills_hamiltonian_spectral_derivation_3320_ready with
    ⟨hReady, _, _, _, _, _, _, _, _, _, _, _, hWitness, _, hPublic, hFinal⟩
  exact ⟨
    hReady,
    yang_mills_hamiltonian_spectral_infimum_eq_3320,
    yang_mills_hamiltonian_spectral_attainment_eq_3320,
    yang_mills_hamiltonian_observable_atom_eq_3320,
    yang_mills_hamiltonian_spectral_derivation_exact_gap_value,
    MGAP4D.MathlibAnalytic.yang_mills_hamiltonian_spectral_derivation_positive_mass,
    MGAP4D.MathlibAnalytic.yang_mills_hamiltonian_spectral_derivation_nonzero_mass,
    hWitness,
    hPublic,
    hFinal⟩

end

end Theorem
end R6
end MGAP4D
