import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanVacuumProjectorOperatorNormConvergenceL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter Topology
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

/-- The actual beta-zero random-scan connected `L²` correlation after `n` steps.
The subtracted term is the rank-one Gibbs-vacuum contribution. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanConnectedCorrelationL2
    (n : ℕ)
    (f g : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) : ℝ :=
  inner ℝ f
      ((periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n)
        g) -
    inner ℝ f
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 *
      inner ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
        g

/-- The connected correlation is exactly the matrix coefficient of the
full-space error operator `P^n - E₀`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanConnectedCorrelationL2_eq_inner_error
    (n : ℕ)
    (f g : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanConnectedCorrelationL2
        n f g =
      inner ℝ f
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
          n g) := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanConnectedCorrelationL2
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
  change
    inner ℝ f
        ((periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n)
          g) -
      inner ℝ f
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 *
        inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          g =
    inner ℝ f
      (((periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n)
          g) -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 g)
  rw [inner_sub_right]
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_inner_smul_vacuum]
  rw [real_inner_smul_right]
  ring

/-- Every beta-zero connected `L²` correlation decays at the exact `n`-step
SLEM factor. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_randomScanConnectedCorrelationL2_le_nStepSLEM_mul_norm_mul_norm
    (n : ℕ)
    (f g : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanConnectedCorrelationL2
        n f g| ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2 n *
        ‖f‖ * ‖g‖ := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanConnectedCorrelationL2_eq_inner_error]
  have hError :
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
          n g‖ ≤
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2 n *
          ‖g‖ := by
    change
      ‖(periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n)
            g -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            0 g‖ ≤
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2 n *
          ‖g‖
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPowL2_apply_sub_vacuumProjector_le_nStepSLEM_mul_norm
        n g
  calc
    |inner ℝ f
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
          n g)| ≤
      ‖f‖ *
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
          n g‖ :=
      abs_real_inner_le_norm f
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
          n g)
    _ ≤ ‖f‖ *
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2 n *
          ‖g‖) :=
      mul_le_mul_of_nonneg_left hError (norm_nonneg f)
    _ = periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2 n *
        ‖f‖ * ‖g‖ := by ring

/-- Explicit numerical form of the sharp connected-correlation decay bound. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_randomScanConnectedCorrelationL2_le_323_div_324_pow_mul_norm_mul_norm
    (n : ℕ)
    (f g : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanConnectedCorrelationL2
        n f g| ≤
      ((323 : ℝ) / 324) ^ n * ‖f‖ * ‖g‖ := by
  simpa [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSLEML2] using
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_randomScanConnectedCorrelationL2_le_nStepSLEM_mul_norm_mul_norm
      n f g

/-- A single nonzero cardinality-one vector attains the connected-correlation
bound at every time, so the factor `(323 / 324)^n` is sharp. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanConnectedCorrelationL2_eq_nStepSLEM_mul_norm_sq :
    ∃ f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      f ≠ 0 ∧
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          f = 0 ∧
      ∀ n : ℕ,
        |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanConnectedCorrelationL2
            n f f| =
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2 n *
            ‖f‖ ^ 2 := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_secondEigenspaceL2_inner_vacuum_eq_zero
    with ⟨f, hfNe, hfSecond, hfOrthogonal⟩
  refine ⟨f, hfNe, hfOrthogonal, ?_⟩
  intro n
  have hfCardinalityOne :
      f ∈ periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCardinalityEigenspaceL2
        1 := by
    rw [←
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSecondEigenspaceL2_eq_cardinalityOne]
    exact hfSecond
  have hAction :
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n)
          f =
        (1 - (1 : ℝ) / 324) ^ n • f :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowL2_apply_eq_smul_of_mem_cardinalityEigenspace
      1 n f hfCardinalityOne
  have hfOrthogonalReverse :
      inner ℝ f
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 = 0 := by
    rw [real_inner_comm]
    exact hfOrthogonal
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanConnectedCorrelationL2
  rw [hfOrthogonal, hfOrthogonalReverse, mul_zero, sub_zero, hAction,
    real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hScalarNonneg :
      0 ≤ (1 - (1 : ℝ) / 324) ^ n :=
    pow_nonneg (by norm_num) n
  rw [abs_of_nonneg (mul_nonneg hScalarNonneg (sq_nonneg ‖f‖))]
  norm_num [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSLEML2]

/-- Every beta-zero connected `L²` correlation converges to zero. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanConnectedCorrelationL2_tendsto_zero
    (f g : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    Tendsto
      (fun n : ℕ =>
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanConnectedCorrelationL2
          n f g)
      atTop
      (𝓝 0) := by
  apply squeeze_zero_norm
  · intro n
    rw [Real.norm_eq_abs]
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_randomScanConnectedCorrelationL2_le_nStepSLEM_mul_norm_mul_norm
        n f g
  · simpa [mul_assoc] using
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanNStepSLEML2_tendsto_zero.mul_const
        (‖f‖ * ‖g‖)

/-- Compact receipt for sharp finite-volume beta-zero connected-correlation
decay in Gibbs `L²`. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSharpConnectedCorrelationDecayL2Receipt :
    Prop :=
  (∀ (n : ℕ)
      (f g : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure),
    |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanConnectedCorrelationL2
        n f g| ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2 n *
        ‖f‖ * ‖g‖) ∧
  (∃ f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    f ≠ 0 ∧
    inner ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
        f = 0 ∧
    ∀ n : ℕ,
      |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanConnectedCorrelationL2
          n f f| =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2 n *
          ‖f‖ ^ 2) ∧
  (∀ f g : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    Tendsto
      (fun n : ℕ =>
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanConnectedCorrelationL2
          n f g)
      atTop
      (𝓝 0))

/-- The sharp beta-zero connected-correlation decay receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSharpConnectedCorrelationDecayL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSharpConnectedCorrelationDecayL2Receipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_randomScanConnectedCorrelationL2_le_nStepSLEM_mul_norm_mul_norm,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanConnectedCorrelationL2_eq_nStepSLEM_mul_norm_sq,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanConnectedCorrelationL2_tendsto_zero⟩

end

end MathlibAnalytic
end MGAP4D
