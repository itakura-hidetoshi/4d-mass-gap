import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanCenteredGreenCovarianceL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

/-- Exact quadratic expansion of one Richardson error step for a continuous
linear endomorphism on a real inner-product space. -/
theorem continuousLinearMap_norm_sub_smul_apply_sq
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (A : E →L[ℝ] E)
    (tau : ℝ)
    (x : E) :
    ‖x - tau • A x‖ ^ 2 =
      ‖x‖ ^ 2 -
        2 * tau * inner ℝ (A x) x +
        tau ^ 2 * ‖A x‖ ^ 2 := by
  calc
    ‖x - tau • A x‖ ^ 2 =
        inner ℝ (x - tau • A x) (x - tau • A x) :=
      (real_inner_self_eq_norm_sq _).symm
    _ =
        ‖x‖ ^ 2 -
          2 * tau * inner ℝ (A x) x +
          tau ^ 2 * ‖A x‖ ^ 2 := by
      simp only [
        inner_sub_left,
        inner_sub_right,
        real_inner_smul_left,
        real_inner_smul_right,
        real_inner_self_eq_norm_sq]
      rw [real_inner_comm x (A x)]
      ring

/-- Generic squared Richardson contraction from a coercive lower quadratic-form
bound, a one-cocoercive upper estimate, and the scalar balance identity. -/
theorem continuousLinearMap_richardson_sq_contraction_of_coercive_cocoercive
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (A : E →L[ℝ] E)
    (m tau q : ℝ)
    (hTauSq : 0 ≤ tau ^ 2)
    (hCoeff : tau ^ 2 - 2 * tau ≤ 0)
    (hBalance : 1 + (tau ^ 2 - 2 * tau) * m = q ^ 2)
    (hCoercive :
      ∀ x : E, m * ‖x‖ ^ 2 ≤ inner ℝ (A x) x)
    (hCocoercive :
      ∀ x : E, ‖A x‖ ^ 2 ≤ inner ℝ (A x) x)
    (x : E) :
    ‖x - tau • A x‖ ^ 2 ≤ q ^ 2 * ‖x‖ ^ 2 := by
  have hCocoMul :
      tau ^ 2 * ‖A x‖ ^ 2 ≤
        tau ^ 2 * inner ℝ (A x) x :=
    mul_le_mul_of_nonneg_left (hCocoercive x) hTauSq
  have hCoeffMul :
      (tau ^ 2 - 2 * tau) * inner ℝ (A x) x ≤
        (tau ^ 2 - 2 * tau) * (m * ‖x‖ ^ 2) :=
    mul_le_mul_of_nonpos_left (hCoercive x) hCoeff
  calc
    ‖x - tau • A x‖ ^ 2 =
        ‖x‖ ^ 2 -
          2 * tau * inner ℝ (A x) x +
          tau ^ 2 * ‖A x‖ ^ 2 :=
      continuousLinearMap_norm_sub_smul_apply_sq A tau x
    _ ≤
        ‖x‖ ^ 2 -
          2 * tau * inner ℝ (A x) x +
          tau ^ 2 * inner ℝ (A x) x := by
      exact add_le_add_left hCocoMul _
    _ =
        ‖x‖ ^ 2 +
          (tau ^ 2 - 2 * tau) * inner ℝ (A x) x := by
      ring
    _ ≤
        ‖x‖ ^ 2 +
          (tau ^ 2 - 2 * tau) * (m * ‖x‖ ^ 2) :=
      add_le_add_left hCoeffMul _
    _ =
        (1 + (tau ^ 2 - 2 * tau) * m) * ‖x‖ ^ 2 := by
      ring
    _ = q ^ 2 * ‖x‖ ^ 2 := by
      rw [hBalance]

/-- A squared contraction with a nonnegative factor gives the ordinary norm
contraction. -/
theorem continuousLinearMap_richardson_contraction_of_sq
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (A : E →L[ℝ] E)
    (tau q : ℝ)
    (hq : 0 ≤ q)
    (hSq :
      ∀ x : E,
        ‖x - tau • A x‖ ^ 2 ≤ q ^ 2 * ‖x‖ ^ 2)
    (x : E) :
    ‖x - tau • A x‖ ≤ q * ‖x‖ := by
  have hSq' :
      ‖x - tau • A x‖ ^ 2 ≤
        (q * ‖x‖) ^ 2 := by
    calc
      ‖x - tau • A x‖ ^ 2 ≤ q ^ 2 * ‖x‖ ^ 2 := hSq x
      _ = (q * ‖x‖) ^ 2 := by ring
  have hLeft : 0 ≤ ‖x - tau • A x‖ :=
    norm_nonneg _
  have hRight : 0 ≤ q * ‖x‖ :=
    mul_nonneg hq (norm_nonneg x)
  nlinarith

/-- A Richardson error endomorphism acts by the scalar error multiplier on any
real eigenvector. -/
theorem continuousLinearMap_richardson_apply_eq_smul_of_apply_eq_smul
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (A : E →L[ℝ] E)
    (tau c : ℝ)
    (x : E)
    (hAction : A x = c • x) :
    (ContinuousLinearMap.id ℝ E - tau • A) x =
      (1 - tau * c) • x := by
  change x - tau • A x = (1 - tau * c) • x
  rw [hAction, smul_smul]
  module

/-- The exact optimal constant step for the beta-zero Poisson Richardson
iteration. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2 :
    ℝ :=
  (648 : ℝ) / 325

/-- The exact minimax contraction factor for the beta-zero Poisson Richardson
iteration. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 :
    ℝ :=
  (323 : ℝ) / 325

/-- The Richardson error endomorphism `I - tau A` on the actual beta-zero
Gibbs-vacuum orthogonal sector. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
    (tau : ℝ) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 →L[ℝ]
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 :=
  ContinuousLinearMap.id ℝ
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 -
    tau •
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2

/-- Pointwise action of the beta-zero Richardson error endomorphism. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanRichardsonErrorEndL2_apply
    (tau : ℝ)
    (e : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
        tau e =
      e -
        tau •
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
            e := by
  rfl

/-- Internal sharp coercivity of the actual beta-zero Poisson endomorphism. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inv_324_mul_norm_sq_le_randomScanPoissonVacuumOrthogonalEndL2_inner
    (e : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    ((1 : ℝ) / 324) * ‖e‖ ^ 2 ≤
      inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
          e)
        e := by
  have hOrthogonal :
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          (e : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) = 0 :=
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_mem_vacuumOrthogonalSubmoduleL2_iff
      (e : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)).1
      e.property
  change
    ((1 : ℝ) / 324) *
        ‖(e : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)‖ ^ 2 ≤
      inner ℝ
        ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
            e :
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
          Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
        (e : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonVacuumOrthogonalEndL2_apply]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inv_324_mul_norm_sq_le_randomScanPoissonOperatorL2_quadraticForm_of_inner_vacuum_eq_zero
      (e : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      hOrthogonal

/-- The optimal beta-zero Richardson step has squared contraction factor
`(323 / 325)^2`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonErrorEndL2_sq_contraction
    (e : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
        e‖ ^ 2 ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ 2 *
        ‖e‖ ^ 2 := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanRichardsonErrorEndL2_apply]
  apply
    continuousLinearMap_richardson_sq_contraction_of_coercive_cocoercive
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
      ((1 : ℝ) / 324)
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2
  · norm_num [
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2]
  · norm_num [
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2]
  · norm_num [
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2]
  · exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inv_324_mul_norm_sq_le_randomScanPoissonVacuumOrthogonalEndL2_inner
  · exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonVacuumOrthogonalEndL2_apply_sq_le_inner
  · exact e

/-- The optimal beta-zero Richardson error map contracts every centered error by
exact factor at most `323 / 325`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonErrorEndL2_norm_contraction
    (e : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
        e‖ ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 *
        ‖e‖ := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanRichardsonErrorEndL2_apply]
  apply
    continuousLinearMap_richardson_contraction_of_sq
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2
  · norm_num [
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2]
  · intro x
    simpa only [
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanRichardsonErrorEndL2_apply] using
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonErrorEndL2_sq_contraction
        x
  · exact e

/-- Operator-norm upper bound for the optimal Richardson error map. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonErrorEndL2_le :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2‖ ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 := by
  apply
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2).opNorm_le_bound
  · norm_num [
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2]
  · intro e
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonErrorEndL2_norm_contraction
        e

/-- A cardinality-one mode attains the positive Richardson endpoint
`323 / 325`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_optimalRichardsonErrorEndL2_apply_eq_factor_smul :
    ∃ e : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      e ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
          e =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 •
          e := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanPoissonVacuumOrthogonalEndL2_apply_eq_inv_324_smul
    with ⟨e, heNe, hAction⟩
  refine ⟨e, heNe, ?_⟩
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanRichardsonErrorEndL2_apply,
    hAction]
  unfold
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2
  module

/-- A terminal-cardinality mode attains the negative Richardson endpoint
`-323 / 325`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_optimalRichardsonErrorEndL2_apply_eq_neg_factor_smul :
    ∃ e : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      e ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
          e =
        (-periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2) •
          e := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanPoissonVacuumOrthogonalEndL2_apply_eq_self
    with ⟨e, heNe, hAction⟩
  refine ⟨e, heNe, ?_⟩
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanRichardsonErrorEndL2_apply,
    hAction]
  unfold
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2
  module

/-- The optimal Richardson contraction factor is attained in norm. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_norm_optimalRichardsonErrorEndL2_apply_eq_factor_mul_norm :
    ∃ e : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      e ≠ 0 ∧
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
          e‖ =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 *
          ‖e‖ := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_optimalRichardsonErrorEndL2_apply_eq_factor_smul
    with ⟨e, heNe, hAction⟩
  refine ⟨e, heNe, ?_⟩
  rw [hAction, norm_smul, Real.norm_eq_abs]
  norm_num [
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2]

/-- Exact operator norm of the optimal beta-zero Richardson error map. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonErrorEndL2_eq :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2‖ =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 := by
  apply le_antisymm
  · exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonErrorEndL2_le
  · rcases
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_norm_optimalRichardsonErrorEndL2_apply_eq_factor_mul_norm
      with ⟨e, heNe, hNorm⟩
    have hFundamental :=
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2).le_opNorm
        e
    rw [hNorm] at hFundamental
    have hNormPos : 0 < ‖e‖ := norm_pos_iff.mpr heNe
    nlinarith [
      ContinuousLinearMap.opNorm_nonneg
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2)]

/-- Every uniform Richardson contraction constant, at every real step, is at
least `323 / 325`; hence the displayed step is globally minimax-optimal over
constant-step Richardson maps. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonFactor_le_of_uniform_bound
    (tau C : ℝ)
    (hUniform :
      ∀ e : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
            tau e‖ ≤
          C * ‖e‖) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ≤
      C := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanPoissonVacuumOrthogonalEndL2_apply_eq_inv_324_smul
    with ⟨eLow, heLowNe, hLowAction⟩
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanPoissonVacuumOrthogonalEndL2_apply_eq_self
    with ⟨eHigh, heHighNe, hHighAction⟩
  have hLowRichardson :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
          tau eLow =
        (1 - tau * ((1 : ℝ) / 324)) • eLow := by
    exact
      continuousLinearMap_richardson_apply_eq_smul_of_apply_eq_smul
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
        tau ((1 : ℝ) / 324) eLow hLowAction
  have hHighRichardson :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
          tau eHigh =
        (1 - tau) • eHigh := by
    have hRaw :=
      continuousLinearMap_richardson_apply_eq_smul_of_apply_eq_smul
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
        tau 1 eHigh
        (by simpa using hHighAction)
    simpa using hRaw
  have hLowBound := hUniform eLow
  have hHighBound := hUniform eHigh
  rw [hLowRichardson, norm_smul, Real.norm_eq_abs] at hLowBound
  rw [hHighRichardson, norm_smul, Real.norm_eq_abs] at hHighBound
  have hLowNormPos : 0 < ‖eLow‖ := norm_pos_iff.mpr heLowNe
  have hHighNormPos : 0 < ‖eHigh‖ := norm_pos_iff.mpr heHighNe
  have hLowAbs :
      |1 - tau * ((1 : ℝ) / 324)| ≤ C := by
    nlinarith
  have hHighAbs :
      |1 - tau| ≤ C := by
    nlinarith
  have hLowUpper :
      1 - tau * ((1 : ℝ) / 324) ≤ C :=
    (abs_le.mp hLowAbs).2
  have hHighLower :
      -C ≤ 1 - tau :=
    (abs_le.mp hHighAbs).1
  unfold
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2
  nlinarith

/-- Recursive optimal Richardson propagation of an initial centered error. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorIterateL2 :
    ℕ →
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 →
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2
  | 0 => fun e => e
  | Nat.succ n => fun e =>
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorIterateL2
          n e)

/-- Geometric error estimate for every finite number of optimal Richardson
steps. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonErrorIterateL2_le
    (n : ℕ)
    (e : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorIterateL2
        n e‖ ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n *
        ‖e‖ := by
  induction n with
  | zero =>
      simp [
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorIterateL2]
  | succ n ih =>
      rw [
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorIterateL2]
      calc
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorIterateL2
              n e)‖ ≤
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 *
            ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorIterateL2
              n e‖ :=
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonErrorEndL2_norm_contraction
            _
        _ ≤
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 *
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n *
              ‖e‖) :=
          mul_le_mul_of_nonneg_left ih
            (by
              norm_num [
                periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2])
        _ =
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ Nat.succ n *
            ‖e‖ := by
          rw [pow_succ]
          ring

/-- The exact beta-zero Richardson factor is strictly between zero and one. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ∈
      Set.Ioo 0 1 := by
  constructor <;>
    norm_num [
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2]

/-- Structured receipt for the exact optimal beta-zero Richardson iteration. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonL2Receipt :
    Prop where
  step_size :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2 =
      (648 : ℝ) / 325
  contraction_factor :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 =
      (323 : ℝ) / 325
  contraction :
    ∀ e : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
          e‖ ≤
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 *
          ‖e‖
  exact_operator_norm :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2‖ =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2
  positive_endpoint_attained :
    ∃ e : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      e ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
          e =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 •
          e
  negative_endpoint_attained :
    ∃ e : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      e ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
          e =
        (-periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2) •
          e
  minimax_optimal :
    ∀ tau C : ℝ,
      (∀ e : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
            tau e‖ ≤
          C * ‖e‖) →
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ≤
        C
  finite_iteration_bound :
    ∀ (n : ℕ)
      (e : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2),
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorIterateL2
          n e‖ ≤
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n *
          ‖e‖

/-- The exact optimal beta-zero Richardson receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonL2Receipt := by
  exact
    { step_size := rfl
      contraction_factor := rfl
      contraction :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonErrorEndL2_norm_contraction
      exact_operator_norm :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonErrorEndL2_eq
      positive_endpoint_attained :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_optimalRichardsonErrorEndL2_apply_eq_factor_smul
      negative_endpoint_attained :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_optimalRichardsonErrorEndL2_apply_eq_neg_factor_smul
      minimax_optimal :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonFactor_le_of_uniform_bound
      finite_iteration_bound :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonErrorIterateL2_le }

end

end MathlibAnalytic
end MGAP4D
