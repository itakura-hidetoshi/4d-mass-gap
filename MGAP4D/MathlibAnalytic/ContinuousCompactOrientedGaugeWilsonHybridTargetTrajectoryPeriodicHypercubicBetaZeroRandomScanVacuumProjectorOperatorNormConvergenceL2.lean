import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroVacuumOrthogonalExactRestrictedOperatorNormL2
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanSpectralConvergenceL2
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter Topology
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Removing the coefficient of a unit vector leaves an orthogonal residual. -/
theorem inner_sub_inner_smul_eq_zero_of_norm_eq_one
    (omega f : V)
    (hOmega : ‖omega‖ = 1) :
    inner ℝ omega (f - inner ℝ omega f • omega) = 0 := by
  have hSelf : inner ℝ omega omega = 1 := by
    rw [real_inner_self_eq_norm_sq, hOmega]
    norm_num
  rw [inner_sub_right, real_inner_smul_right, hSelf]
  ring

/-- Orthogonal removal of the coefficient along a unit vector is norm
nonexpansive. -/
theorem norm_sub_inner_smul_le_norm_of_norm_eq_one
    (omega f : V)
    (hOmega : ‖omega‖ = 1) :
    ‖f - inner ℝ omega f • omega‖ ≤ ‖f‖ := by
  let a : ℝ := inner ℝ omega f
  let r : V := f - a • omega
  have hResidual : inner ℝ omega r = 0 := by
    simpa [a, r] using
      inner_sub_inner_smul_eq_zero_of_norm_eq_one omega f hOmega
  have hOrthogonal : inner ℝ (a • omega) r = 0 := by
    rw [real_inner_smul_left, hResidual, mul_zero]
  have hPythagoras :
      ‖a • omega + r‖ ^ 2 = ‖a • omega‖ ^ 2 + ‖r‖ ^ 2 := by
    rw [norm_add_sq_real, hOrthogonal]
    ring
  have hDecomposition : a • omega + r = f := by
    simp [r]
  have hSquare : ‖f‖ ^ 2 = ‖a • omega‖ ^ 2 + ‖r‖ ^ 2 := by
    simpa [hDecomposition] using hPythagoras
  have hr0 : 0 ≤ ‖r‖ := norm_nonneg r
  have hf0 : 0 ≤ ‖f‖ := norm_nonneg f
  nlinarith [sq_nonneg ‖a • omega‖]

/-- Every cardinality-zero component is fixed by every beta-zero random-scan
power. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowL2_apply_fluctuationCardinalityProjectorL2_zero_eq_self
    (n : ℕ)
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n)
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        0 f := by
  apply
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowL2_apply_eq_self_of_mem_stationaryEigenspace
      n
  rw [←
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_range_fluctuationCardinalityProjectorL2_eq_randomScanCardinalityEigenspaceL2
      0 (by omega)]
  exact ⟨f, rfl⟩

/-- Subtracting the cardinality-zero component leaves a vector in the actual
Gibbs-vacuum orthogonal subspace. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_vacuum_sub_fluctuationCardinalityProjectorL2_zero_apply_eq_zero
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    inner ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
        (f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            0 f) = 0 := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_inner_smul_vacuum]
  exact
    inner_sub_inner_smul_eq_zero_of_norm_eq_one
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
      f
      (continuous_compact_oriented_gibbsVacuumL2_norm
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem)

/-- Removing the cardinality-zero vacuum component cannot increase the Gibbs
`L²` norm. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_sub_fluctuationCardinalityProjectorL2_zero_apply_le_norm
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    ‖f -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f‖ ≤ ‖f‖ := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_inner_smul_vacuum]
  exact
    norm_sub_inner_smul_le_norm_of_norm_eq_one
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
      f
      (continuous_compact_oriented_gibbsVacuumL2_norm
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem)

/-- The full-space error operator between the beta-zero random-scan `n`-step
operator and the exact cardinality-zero vacuum projector. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
    (n : ℕ) :
    Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure →L[ℝ]
      Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure :=
  (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n) -
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
      0

/-- The full-space error acts by applying the random-scan power to the
vacuum-orthogonal residual. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowVacuumProjectorErrorL2_apply
    (n : ℕ)
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
        n f =
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n)
        (f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            0 f) := by
  calc
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
        n f =
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n)
          f -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f := rfl
    _ =
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n)
          f -
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n)
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            0 f) := by
      rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowL2_apply_fluctuationCardinalityProjectorL2_zero_eq_self]
    _ =
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n)
        (f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            0 f) := by
      rw [map_sub]

/-- The operator norm of the full-space vacuum-projector error is at most the
exact `n`-step SLEM factor. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPowVacuumProjectorErrorL2_le_nStepSLEM
    (n : ℕ) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
        n‖ ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2 n := by
  apply
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
      n).opNorm_le_bound
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2_nonneg n)
  intro f
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowVacuumProjectorErrorL2_apply]
  calc
    ‖(periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n)
        (f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            0 f)‖ ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2 n *
        ‖f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            0 f‖ :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPowL2_apply_le_nStepSLEM_mul_norm_of_inner_vacuum_eq_zero
        n
        (f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            0 f)
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_vacuum_sub_fluctuationCardinalityProjectorL2_zero_apply_eq_zero
          f)
    _ ≤ periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2 n *
        ‖f‖ :=
      mul_le_mul_of_nonneg_left
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_sub_fluctuationCardinalityProjectorL2_zero_apply_le_norm
          f)
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2_nonneg n)

/-- A nonzero cardinality-one vector attains the full-space error norm, giving the
matching lower bound. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_nStepSLEM_le_norm_randomScanPowVacuumProjectorErrorL2
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2 n ≤
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
        n‖ := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_secondEigenspaceL2_inner_vacuum_eq_zero
    with ⟨f, hfNe, hfSecond, hfOrthogonal⟩
  have hVacuumZero :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f = 0 := by
    rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_inner_smul_vacuum,
      hfOrthogonal, zero_smul]
  have hAttain :
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
          n f‖ =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2 n *
          ‖f‖ := by
    rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowVacuumProjectorErrorL2_apply,
      hVacuumZero, sub_zero]
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPowL2_apply_eq_nStepSLEM_mul_norm_of_mem_secondEigenspace
        n f hfSecond
  have hFundamental :=
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
      n).le_opNorm f
  rw [hAttain] at hFundamental
  have hfNormPos : 0 < ‖f‖ := norm_pos_iff.mpr hfNe
  nlinarith [
    ContinuousLinearMap.opNorm_nonneg
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
        n)]

/-- The exact full-space operator norm error is `(323 / 324)^n`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPowVacuumProjectorErrorL2_eq_nStepSLEM
    (n : ℕ) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
        n‖ =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2 n := by
  exact le_antisymm
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPowVacuumProjectorErrorL2_le_nStepSLEM
      n)
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_nStepSLEM_le_norm_randomScanPowVacuumProjectorErrorL2
      n)

/-- Explicit numerical form of the exact full-space operator norm error. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPowVacuumProjectorErrorL2_eq_323_div_324_pow
    (n : ℕ) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
        n‖ = ((323 : ℝ) / 324) ^ n := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPowVacuumProjectorErrorL2_eq_nStepSLEM]
  norm_num [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSLEML2]

/-- The beta-zero random-scan powers converge in operator norm to the exact
cardinality-zero vacuum projector. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowL2_tendsto_fluctuationCardinalityProjectorL2_zero_operatorNorm :
    Tendsto
      (fun n : ℕ =>
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n)
      atTop
      (𝓝
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0)) := by
  have hError :
      Tendsto
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
        atTop
        (𝓝 0) := by
    apply squeeze_zero_norm
    · intro n
      exact le_of_eq
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPowVacuumProjectorErrorL2_eq_nStepSLEM
          n)
    · exact
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanNStepSLEML2_tendsto_zero
  have hAdd := hError.add_const
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
      0)
  simpa [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2] using
    hAdd

/-- Every input has an explicit geometric error bound relative to its exact
vacuum projection. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPowL2_apply_sub_vacuumProjector_le_nStepSLEM_mul_norm
    (n : ℕ)
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    ‖(periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n)
          f -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f‖ ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2 n *
        ‖f‖ := by
  change
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
        n f‖ ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2 n *
        ‖f‖
  calc
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
        n f‖ ≤
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
        n‖ * ‖f‖ :=
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
        n).le_opNorm f
    _ = periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2 n *
        ‖f‖ := by
      rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPowVacuumProjectorErrorL2_eq_nStepSLEM]

/-- Every beta-zero random-scan orbit converges strongly to its exact vacuum
component. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowL2_apply_tendsto_fluctuationCardinalityProjectorL2_zero
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    Tendsto
      (fun n : ℕ =>
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n)
          f)
      atTop
      (𝓝
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f)) := by
  have hError :
      Tendsto
        (fun n : ℕ =>
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n)
              f -
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
              0 f)
        atTop
        (𝓝 0) := by
    apply squeeze_zero_norm
    · intro n
      exact
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPowL2_apply_sub_vacuumProjector_le_nStepSLEM_mul_norm
          n f
    · simpa using
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanNStepSLEML2_tendsto_zero.mul_const
          ‖f‖
  have hAdd := hError.add_const
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
      0 f)
  simpa using hAdd

/-- Rank-one explicit form of the global strong limit. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowL2_apply_tendsto_inner_vacuum_smul_vacuum
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    Tendsto
      (fun n : ℕ =>
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n)
          f)
      atTop
      (𝓝
        (inner ℝ
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
            f •
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2)) := by
  simpa [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_inner_smul_vacuum] using
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowL2_apply_tendsto_fluctuationCardinalityProjectorL2_zero
      f

/-- Compact receipt for exact operator-norm convergence of beta-zero random-scan
powers to the normalized Gibbs-vacuum projector. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanVacuumProjectorOperatorNormConvergenceL2Receipt :
    Prop :=
  (∀ n : ℕ,
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
        n‖ =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2 n) ∧
  Tendsto
      (fun n : ℕ =>
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n)
      atTop
      (𝓝
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0)) ∧
  (∀ f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    Tendsto
      (fun n : ℕ =>
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n)
          f)
      atTop
      (𝓝
        (inner ℝ
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
            f •
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2)))

/-- The exact beta-zero vacuum-projector operator-norm convergence receipt is
proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanVacuumProjectorOperatorNormConvergenceL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanVacuumProjectorOperatorNormConvergenceL2Receipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPowVacuumProjectorErrorL2_eq_nStepSLEM,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowL2_tendsto_fluctuationCardinalityProjectorL2_zero_operatorNorm,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowL2_apply_tendsto_inner_vacuum_smul_vacuum⟩

end

end MathlibAnalytic
end MGAP4D
