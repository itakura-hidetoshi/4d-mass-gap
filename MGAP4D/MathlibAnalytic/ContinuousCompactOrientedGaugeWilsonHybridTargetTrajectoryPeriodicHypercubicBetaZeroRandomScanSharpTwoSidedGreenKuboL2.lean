import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanSharpGreenKuboL2
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter Topology
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

/-- The positive-lag beta-zero random-scan SLEM geometric series is summable. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_summable_323_div_324_pow_succ :
    Summable (fun n : ℕ => ((323 : ℝ) / 324) ^ (n + 1)) := by
  have h :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_summable_323_div_324_pow.mul_right
      ((323 : ℝ) / 324)
  simpa [pow_succ] using h

/-- The positive-lag beta-zero random-scan SLEM mass is exactly `323`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_tsum_323_div_324_pow_succ_eq_323 :
    ∑' n : ℕ, ((323 : ℝ) / 324) ^ (n + 1) = 323 := by
  calc
    (∑' n : ℕ, ((323 : ℝ) / 324) ^ (n + 1)) =
        ∑' n : ℕ, ((323 : ℝ) / 324) ^ n * ((323 : ℝ) / 324) := by
      apply tsum_congr
      intro n
      rw [pow_succ]
    _ = (∑' n : ℕ, ((323 : ℝ) / 324) ^ n) * ((323 : ℝ) / 324) := by
      rw [tsum_mul_right]
    _ = 323 := by
      rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_tsum_323_div_324_pow_eq_324]
      norm_num

/-- Every positive-lag beta-zero connected `L²` correlation sequence is
absolutely summable. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_summable_abs_randomScanConnectedCorrelationL2_succ
    (f g : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    Summable
      (fun n : ℕ =>
        |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanConnectedCorrelationL2
          (n + 1) f g|) := by
  let M : ℝ := ‖f‖ * ‖g‖
  have hGeom :
      Summable (fun n : ℕ => ((323 : ℝ) / 324) ^ (n + 1) * M) :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_summable_323_div_324_pow_succ.mul_right
      M
  apply Summable.of_norm_bounded hGeom
  intro n
  simpa [Real.norm_eq_abs, M, mul_assoc] using
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_randomScanConnectedCorrelationL2_le_323_div_324_pow_mul_norm_mul_norm
      (n + 1) f g

/-- The positive-lag absolute connected-correlation mass is bounded by the
sharp geometric constant `323`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_tsum_abs_randomScanConnectedCorrelationL2_succ_le_323_mul_norm_mul_norm
    (f g : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    (∑' n : ℕ,
      |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanConnectedCorrelationL2
        (n + 1) f g|) ≤
      323 * ‖f‖ * ‖g‖ := by
  let M : ℝ := ‖f‖ * ‖g‖
  have hAbs :
      Summable
        (fun n : ℕ =>
          |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanConnectedCorrelationL2
            (n + 1) f g|) :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_summable_abs_randomScanConnectedCorrelationL2_succ
      f g
  have hGeom :
      Summable (fun n : ℕ => ((323 : ℝ) / 324) ^ (n + 1) * M) :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_summable_323_div_324_pow_succ.mul_right
      M
  calc
    (∑' n : ℕ,
      |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanConnectedCorrelationL2
        (n + 1) f g|) ≤
        ∑' n : ℕ, ((323 : ℝ) / 324) ^ (n + 1) * M := by
      exact Summable.tsum_le_tsum
        (fun n => by
          simpa [M, mul_assoc] using
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_randomScanConnectedCorrelationL2_le_323_div_324_pow_mul_norm_mul_norm
              (n + 1) f g)
        hAbs hGeom
    _ = (∑' n : ℕ, ((323 : ℝ) / 324) ^ (n + 1)) * M := by
      rw [tsum_mul_right]
    _ = 323 * ‖f‖ * ‖g‖ := by
      rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_tsum_323_div_324_pow_succ_eq_323]
      simp [M, mul_assoc]

/-- The positive-lag beta-zero Green--Kubo matrix coefficient. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPositiveLagGreenKuboL2
    (f g : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) : ℝ :=
  ∑' n : ℕ,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanConnectedCorrelationL2
      (n + 1) f g

/-- The positive-lag Green--Kubo coefficient has norm at most `323` times the
input norms. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_randomScanPositiveLagGreenKuboL2_le_323_mul_norm_mul_norm
    (f g : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPositiveLagGreenKuboL2
        f g| ≤
      323 * ‖f‖ * ‖g‖ := by
  have hNormSummable :
      Summable
        (fun n : ℕ =>
          ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanConnectedCorrelationL2
            (n + 1) f g‖) := by
    simpa [Real.norm_eq_abs] using
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_summable_abs_randomScanConnectedCorrelationL2_succ
        f g
  have hTriangle := norm_tsum_le_tsum_norm hNormSummable
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPositiveLagGreenKuboL2
  rw [Real.norm_eq_abs] at hTriangle
  exact hTriangle.trans
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_tsum_abs_randomScanConnectedCorrelationL2_succ_le_323_mul_norm_mul_norm
      f g)

/-- The beta-zero two-sided Green--Kubo self-correlation coefficient. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanTwoSidedGreenKuboL2
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) : ℝ :=
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanConnectedCorrelationL2
      0 f f +
    2 *
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPositiveLagGreenKuboL2
        f f

/-- The beta-zero two-sided Green--Kubo coefficient is bounded by the sharp
constant `647 = 1 + 2 * 323`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_randomScanTwoSidedGreenKuboL2_le_647_mul_norm_sq
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanTwoSidedGreenKuboL2
        f| ≤
      647 * ‖f‖ ^ 2 := by
  have hZero :
      |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanConnectedCorrelationL2
        0 f f| ≤ ‖f‖ ^ 2 := by
    simpa [pow_two] using
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_randomScanConnectedCorrelationL2_le_323_div_324_pow_mul_norm_mul_norm
        0 f f
  have hPositive :
      |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPositiveLagGreenKuboL2
        f f| ≤
      323 * ‖f‖ ^ 2 := by
    simpa [pow_two, mul_assoc] using
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_randomScanPositiveLagGreenKuboL2_le_323_mul_norm_mul_norm
        f f
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanTwoSidedGreenKuboL2
  calc
    |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanConnectedCorrelationL2
          0 f f +
        2 *
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPositiveLagGreenKuboL2
            f f| ≤
      |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanConnectedCorrelationL2
          0 f f| +
        |2 *
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPositiveLagGreenKuboL2
            f f| := by
      simpa [Real.norm_eq_abs] using
        norm_add_le
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanConnectedCorrelationL2
            0 f f)
          (2 *
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPositiveLagGreenKuboL2
              f f)
    _ =
      |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanConnectedCorrelationL2
          0 f f| +
        2 *
          |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPositiveLagGreenKuboL2
            f f| := by
      norm_num [abs_mul]
    _ ≤ ‖f‖ ^ 2 + 2 * (323 * ‖f‖ ^ 2) := by
      exact add_le_add hZero
        (mul_le_mul_of_nonneg_left hPositive (by norm_num))
    _ = 647 * ‖f‖ ^ 2 := by ring

/-- A cardinality-one vector has the exact signed geometric connected
self-correlation at every time. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanConnectedCorrelationL2_eq_323_div_324_pow_mul_norm_sq :
    ∃ f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      f ≠ 0 ∧
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          f = 0 ∧
      ∀ n : ℕ,
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanConnectedCorrelationL2
            n f f =
          ((323 : ℝ) / 324) ^ n * ‖f‖ ^ 2 := by
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
  have hAction :=
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
  norm_num

/-- A single nonzero cardinality-one vector attains the two-sided Green--Kubo
constant `647`, so the bound is sharp. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanTwoSidedGreenKuboL2_eq_647_mul_norm_sq :
    ∃ f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      f ≠ 0 ∧
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          f = 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanTwoSidedGreenKuboL2
          f =
        647 * ‖f‖ ^ 2 := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanConnectedCorrelationL2_eq_323_div_324_pow_mul_norm_sq
    with ⟨f, hfNe, hfOrthogonal, hPointwise⟩
  refine ⟨f, hfNe, hfOrthogonal, ?_⟩
  have hZero :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanConnectedCorrelationL2
          0 f f =
        ‖f‖ ^ 2 := by
    simpa using hPointwise 0
  have hPositive :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPositiveLagGreenKuboL2
          f f =
        323 * ‖f‖ ^ 2 := by
    unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPositiveLagGreenKuboL2
    calc
      (∑' n : ℕ,
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanConnectedCorrelationL2
          (n + 1) f f) =
          ∑' n : ℕ, ((323 : ℝ) / 324) ^ (n + 1) * ‖f‖ ^ 2 := by
        apply tsum_congr
        intro n
        rw [hPointwise (n + 1)]
      _ = (∑' n : ℕ, ((323 : ℝ) / 324) ^ (n + 1)) * ‖f‖ ^ 2 := by
        rw [tsum_mul_right]
      _ = 323 * ‖f‖ ^ 2 := by
        rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_tsum_323_div_324_pow_succ_eq_323]
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanTwoSidedGreenKuboL2
  rw [hZero, hPositive]
  ring

/-- Compact receipt for the sharp two-sided beta-zero Green--Kubo bound. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSharpTwoSidedGreenKuboL2Receipt :
    Prop :=
  (∀ f g : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    (∑' n : ℕ,
      |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanConnectedCorrelationL2
        (n + 1) f g|) ≤
      323 * ‖f‖ * ‖g‖) ∧
  (∀ f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanTwoSidedGreenKuboL2
        f| ≤
      647 * ‖f‖ ^ 2) ∧
  (∃ f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    f ≠ 0 ∧
    inner ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
        f = 0 ∧
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanTwoSidedGreenKuboL2
        f =
      647 * ‖f‖ ^ 2)

/-- The sharp two-sided beta-zero Green--Kubo receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSharpTwoSidedGreenKuboL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSharpTwoSidedGreenKuboL2Receipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_tsum_abs_randomScanConnectedCorrelationL2_succ_le_323_mul_norm_mul_norm,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_randomScanTwoSidedGreenKuboL2_le_647_mul_norm_sq,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanTwoSidedGreenKuboL2_eq_647_mul_norm_sq⟩

end

end MathlibAnalytic
end MGAP4D
