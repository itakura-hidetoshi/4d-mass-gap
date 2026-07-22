import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanSharpConnectedCorrelationDecayL2
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter Topology
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

/-- The exact beta-zero random-scan SLEM geometric series is summable. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_summable_323_div_324_pow :
    Summable (fun n : ℕ => ((323 : ℝ) / 324) ^ n) := by
  exact summable_geometric_of_lt_one (by norm_num) (by norm_num)

/-- The one-sided beta-zero random-scan SLEM mass is exactly `324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_tsum_323_div_324_pow_eq_324 :
    ∑' n : ℕ, ((323 : ℝ) / 324) ^ n = 324 := by
  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

/-- Every beta-zero connected `L²` correlation sequence is absolutely summable. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_summable_abs_randomScanConnectedCorrelationL2
    (f g : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    Summable
      (fun n : ℕ =>
        |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanConnectedCorrelationL2
          n f g|) := by
  let M : ℝ := ‖f‖ * ‖g‖
  have hGeom : Summable (fun n : ℕ => ((323 : ℝ) / 324) ^ n * M) :=
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_summable_323_div_324_pow).mul_right M
  apply Summable.of_norm_bounded hGeom
  intro n
  simpa [Real.norm_eq_abs, M, mul_assoc] using
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_randomScanConnectedCorrelationL2_le_323_div_324_pow_mul_norm_mul_norm
      n f g

/-- Every beta-zero connected `L²` correlation sequence itself is summable. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_summable_randomScanConnectedCorrelationL2
    (f g : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    Summable
      (fun n : ℕ =>
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanConnectedCorrelationL2
          n f g) := by
  let M : ℝ := ‖f‖ * ‖g‖
  have hGeom : Summable (fun n : ℕ => ((323 : ℝ) / 324) ^ n * M) :=
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_summable_323_div_324_pow).mul_right M
  apply Summable.of_norm_bounded hGeom
  intro n
  simpa [Real.norm_eq_abs, M, mul_assoc] using
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_randomScanConnectedCorrelationL2_le_323_div_324_pow_mul_norm_mul_norm
      n f g

/-- The one-sided absolute connected-correlation mass is bounded by the sharp
geometric constant `324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_tsum_abs_randomScanConnectedCorrelationL2_le_324_mul_norm_mul_norm
    (f g : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    (∑' n : ℕ,
      |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanConnectedCorrelationL2
        n f g|) ≤
      324 * ‖f‖ * ‖g‖ := by
  let M : ℝ := ‖f‖ * ‖g‖
  have hAbs : Summable
      (fun n : ℕ =>
        |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanConnectedCorrelationL2
          n f g|) :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_summable_abs_randomScanConnectedCorrelationL2
      f g
  have hGeom : Summable (fun n : ℕ => ((323 : ℝ) / 324) ^ n * M) :=
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_summable_323_div_324_pow).mul_right M
  calc
    (∑' n : ℕ,
      |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanConnectedCorrelationL2
        n f g|) ≤
        ∑' n : ℕ, ((323 : ℝ) / 324) ^ n * M := by
      exact Summable.tsum_le_tsum
        (fun n => by
          simpa [M, mul_assoc] using
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_randomScanConnectedCorrelationL2_le_323_div_324_pow_mul_norm_mul_norm
              n f g)
        hAbs hGeom
    _ = (∑' n : ℕ, ((323 : ℝ) / 324) ^ n) * M := by
      rw [tsum_mul_right]
    _ = 324 * ‖f‖ * ‖g‖ := by
      rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_tsum_323_div_324_pow_eq_324]
      simp [M, mul_assoc]

/-- The one-sided beta-zero Green--Kubo matrix coefficient. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOneSidedGreenKuboL2
    (f g : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) : ℝ :=
  ∑' n : ℕ,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanConnectedCorrelationL2
      n f g

/-- The one-sided Green--Kubo coefficient has norm at most the sharp geometric
constant `324` times the input norms. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_randomScanOneSidedGreenKuboL2_le_324_mul_norm_mul_norm
    (f g : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOneSidedGreenKuboL2
        f g| ≤
      324 * ‖f‖ * ‖g‖ := by
  have hNormSummable : Summable
      (fun n : ℕ =>
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanConnectedCorrelationL2
          n f g‖) := by
    simpa [Real.norm_eq_abs] using
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_summable_abs_randomScanConnectedCorrelationL2
        f g
  have hTriangle := norm_tsum_le_tsum_norm hNormSummable
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOneSidedGreenKuboL2
  rw [Real.norm_eq_abs] at hTriangle
  exact hTriangle.trans
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_tsum_abs_randomScanConnectedCorrelationL2_le_324_mul_norm_mul_norm
      f g)

/-- A single nonzero cardinality-one vector attains the one-sided absolute
Green--Kubo mass `324 * ‖f‖²`, so the constant `324` is sharp. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_tsum_abs_randomScanConnectedCorrelationL2_eq_324_mul_norm_sq :
    ∃ f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      f ≠ 0 ∧
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          f = 0 ∧
      (∑' n : ℕ,
        |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanConnectedCorrelationL2
          n f f|) =
        324 * ‖f‖ ^ 2 := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanConnectedCorrelationL2_eq_nStepSLEM_mul_norm_sq
    with ⟨f, hfNe, hfOrthogonal, hPointwise⟩
  refine ⟨f, hfNe, hfOrthogonal, ?_⟩
  calc
    (∑' n : ℕ,
      |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanConnectedCorrelationL2
        n f f|) =
        ∑' n : ℕ, ((323 : ℝ) / 324) ^ n * ‖f‖ ^ 2 := by
      apply tsum_congr
      intro n
      rw [hPointwise n]
      norm_num [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2,
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSLEML2]
    _ = (∑' n : ℕ, ((323 : ℝ) / 324) ^ n) * ‖f‖ ^ 2 := by
      rw [tsum_mul_right]
    _ = 324 * ‖f‖ ^ 2 := by
      rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_tsum_323_div_324_pow_eq_324]

/-- Compact receipt for sharp one-sided beta-zero Green--Kubo summability. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSharpGreenKuboL2Receipt :
    Prop :=
  (∀ f g : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    Summable
      (fun n : ℕ =>
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanConnectedCorrelationL2
          n f g)) ∧
  (∀ f g : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    (∑' n : ℕ,
      |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanConnectedCorrelationL2
        n f g|) ≤
      324 * ‖f‖ * ‖g‖) ∧
  (∀ f g : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOneSidedGreenKuboL2
        f g| ≤
      324 * ‖f‖ * ‖g‖) ∧
  (∃ f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    f ≠ 0 ∧
    inner ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
        f = 0 ∧
    (∑' n : ℕ,
      |periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanConnectedCorrelationL2
        n f f|) =
      324 * ‖f‖ ^ 2)

/-- The sharp one-sided beta-zero Green--Kubo receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSharpGreenKuboL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSharpGreenKuboL2Receipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_summable_randomScanConnectedCorrelationL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_tsum_abs_randomScanConnectedCorrelationL2_le_324_mul_norm_mul_norm,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_abs_randomScanOneSidedGreenKuboL2_le_324_mul_norm_mul_norm,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_tsum_abs_randomScanConnectedCorrelationL2_eq_324_mul_norm_sq⟩

end

end MathlibAnalytic
end MGAP4D
