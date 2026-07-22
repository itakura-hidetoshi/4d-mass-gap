import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroVacuumOrthogonalRandomScanNStepContractionL2
import MGAP4D.MathlibAnalytic.FiniteWilsonVacuumOrthogonalInvariance
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

/-- The actual beta-zero Gibbs `L²` vacuum-orthogonal submodule. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalSubmoduleL2 :
    Submodule ℝ
      (Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :=
  finiteVacuumOrthogonal
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2

/-- The actual beta-zero Gibbs `L²` vacuum-orthogonal carrier. -/
abbrev periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 : Type :=
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalSubmoduleL2

/-- Membership in the actual vacuum-orthogonal submodule is exactly vanishing of
its Gibbs-vacuum coefficient. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_mem_vacuumOrthogonalSubmoduleL2_iff
    (f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    f ∈ periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalSubmoduleL2 ↔
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          f = 0 := by
  exact finite_wilson_mem_vacuumOrthogonal_iff
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 f

/-- The `n`-step random-scan operator with its domain restricted to the actual
vacuum-orthogonal Gibbs `L²` subspace.  The codomain remains the ambient Gibbs
`L²` space, so this is the standard domain-restricted operator norm. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumOrthogonalRestrictionL2
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 →L[ℝ]
      Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure :=
  (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n).comp
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalSubmoduleL2.subtypeL

/-- The bundled restriction acts by the ambient `n`-step random-scan operator. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowVacuumOrthogonalRestrictionL2_apply
    (n : ℕ)
    (f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumOrthogonalRestrictionL2
        n f =
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n)
        (f : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) := by
  rfl

/-- The largest nonstationary cardinality-one sector contains a nonzero vector
which is orthogonal to the normalized Gibbs vacuum. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_secondEigenspaceL2_inner_vacuum_eq_zero :
    ∃ f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      f ≠ 0 ∧
      f ∈ periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSecondEigenspaceL2 ∧
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          f = 0 := by
  have hPoint :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSecondSpectralValueL2 ∈
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPointSpectrumL2 := by
    rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPointSpectrumL2_eq_allowed_affine_grid]
    refine ⟨⟨1, by omega⟩, ?_⟩
    simp [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSecondSpectralValueL2]
  change ∃ f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    f ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 f =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSecondSpectralValueL2 • f
    at hPoint
  rcases hPoint with ⟨f, hfNe, hfEigen⟩
  have hfSecond :
      f ∈ periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSecondEigenspaceL2 := by
    rw [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSecondEigenspaceL2,
      Module.End.mem_genEigenspace_one]
    exact hfEigen
  have hfCardinalityOne :
      f ∈ periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCardinalityEigenspaceL2
        1 := by
    rw [←
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSecondEigenspaceL2_eq_cardinalityOne]
    exact hfSecond
  have hfRange :
      f ∈ LinearMap.range
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          1).toLinearMap := by
    rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_range_fluctuationCardinalityProjectorL2_eq_randomScanCardinalityEigenspaceL2
      1 (by omega)]
    exact hfCardinalityOne
  rcases hfRange with ⟨g, hg⟩
  have hVacuumProjector :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 =
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 := by
    rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_inner_smul_vacuum]
    have hInner :
        inner ℝ
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 = 1 := by
      rw [real_inner_self_eq_norm_sq]
      rw [continuous_compact_oriented_gibbsVacuumL2_norm
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem]
      norm_num
    rw [hInner, one_smul]
  have hOrthogonal :
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          f = 0 := by
    rw [← hg, ← hVacuumProjector]
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_vacuumComponent_fluctuationCardinalityProjectorL2_eq_zero_of_pos
        1 (by omega)
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 g
  exact ⟨f, hfNe, hfSecond, hOrthogonal⟩

/-- The operator norm of the `n`-step random-scan restriction to `Ω⊥` is at most
the exact `n`-step SLEM factor. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPowVacuumOrthogonalRestrictionL2_le_nStepSLEM
    (n : ℕ) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumOrthogonalRestrictionL2
        n‖ ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2 n := by
  apply
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumOrthogonalRestrictionL2
      n).opNorm_le_bound
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2_nonneg n)
  intro f
  change
    ‖(periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n)
        (f : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)‖ ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2 n * ‖f‖
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPowL2_apply_le_nStepSLEM_mul_norm_of_inner_vacuum_eq_zero
      n
      (f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      ((periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_mem_vacuumOrthogonalSubmoduleL2_iff
        (f : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)).1
        f.property)

/-- The cardinality-one eigenvector attains the exact `n`-step SLEM factor, so
the exact factor is at most the restricted operator norm. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_nStepSLEM_le_norm_randomScanPowVacuumOrthogonalRestrictionL2
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2 n ≤
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumOrthogonalRestrictionL2
        n‖ := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_secondEigenspaceL2_inner_vacuum_eq_zero
    with ⟨f, hfNe, hfSecond, hfOrthogonal⟩
  let fOrthogonal :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 :=
    ⟨f,
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_mem_vacuumOrthogonalSubmoduleL2_iff
        f).2 hfOrthogonal⟩
  have hfOrthogonalNe : fOrthogonal ≠ 0 := by
    intro hZero
    apply hfNe
    have hCoe := congrArg
      (fun x : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 =>
        (x : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure))
      hZero
    simpa [fOrthogonal] using hCoe
  have hNormPos : 0 < ‖fOrthogonal‖ := norm_pos_iff.mpr hfOrthogonalNe
  have hAttain :
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumOrthogonalRestrictionL2
          n fOrthogonal‖ =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2 n *
          ‖fOrthogonal‖ := by
    change
      ‖(periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n)
          f‖ =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2 n * ‖f‖
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPowL2_apply_eq_nStepSLEM_mul_norm_of_mem_secondEigenspace
        n f hfSecond
  have hFundamental :=
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumOrthogonalRestrictionL2
      n).le_opNorm fOrthogonal
  rw [hAttain] at hFundamental
  nlinarith [
    ContinuousLinearMap.opNorm_nonneg
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumOrthogonalRestrictionL2
        n)]

/-- The exact operator norm of the actual beta-zero `n`-step random-scan operator
with domain restricted to the Gibbs-vacuum orthogonal subspace is
`(323 / 324)^n`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPowVacuumOrthogonalRestrictionL2_eq_nStepSLEM
    (n : ℕ) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumOrthogonalRestrictionL2
        n‖ =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2 n := by
  exact le_antisymm
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPowVacuumOrthogonalRestrictionL2_le_nStepSLEM
      n)
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_nStepSLEM_le_norm_randomScanPowVacuumOrthogonalRestrictionL2
      n)

/-- Explicit numerical form of the exact restricted `n`-step operator norm. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPowVacuumOrthogonalRestrictionL2_eq_323_div_324_pow
    (n : ℕ) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumOrthogonalRestrictionL2
        n‖ = ((323 : ℝ) / 324) ^ n := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPowVacuumOrthogonalRestrictionL2_eq_nStepSLEM]
  norm_num [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSLEML2]

/-- One-step exact restricted operator norm. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanVacuumOrthogonalRestrictionL2_eq_slem :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumOrthogonalRestrictionL2
        1‖ =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSLEML2 := by
  simpa [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2] using
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPowVacuumOrthogonalRestrictionL2_eq_nStepSLEM
      1

/-- Compact receipt for the exact beta-zero random-scan operator norm on the
full Gibbs-vacuum orthogonal subspace. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalExactRestrictedOperatorNormL2Receipt :
    Prop :=
  ∀ n : ℕ,
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumOrthogonalRestrictionL2
        n‖ =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2 n

/-- The exact restricted-operator-norm receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalExactRestrictedOperatorNormL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalExactRestrictedOperatorNormL2Receipt := by
  intro n
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPowVacuumOrthogonalRestrictionL2_eq_nStepSLEM
      n

end

end MathlibAnalytic
end MGAP4D
