import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanOptimalRichardsonMinimalStoppingIndicesL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000

/-- The closed logarithmic threshold for the geometric inequality
`C * q^n ≤ epsilon`, before taking a natural ceiling. -/
noncomputable def realGeometricLogarithmicThreshold
    (q C epsilon : ℝ) : ℝ :=
  Real.log (C / epsilon) / (-Real.log q)

/-- The natural ceiling of the closed logarithmic geometric threshold. -/
noncomputable def realGeometricCeilingIterationCount
    (q C epsilon : ℝ) : ℕ :=
  ⌈realGeometricLogarithmicThreshold q C epsilon⌉₊

/-- For positive `C`, positive tolerance, and `0 < q < 1`, the logarithmic
threshold inequality is exactly equivalent to the geometric bound. -/
theorem realGeometricLogarithmicThreshold_le_nat_iff
    (q C epsilon : ℝ)
    (hqPos : 0 < q)
    (hqLtOne : q < 1)
    (hC : 0 < C)
    (hEpsilon : 0 < epsilon)
    (n : ℕ) :
    realGeometricLogarithmicThreshold q C epsilon ≤ (n : ℝ) ↔
      C * q ^ n ≤ epsilon := by
  have hLogNeg : Real.log q < 0 :=
    Real.log_neg hqPos hqLtOne
  have hDenPos : 0 < -Real.log q := neg_pos.mpr hLogNeg
  have hPowPos : 0 < q ^ n := pow_pos hqPos n
  have hQuotPos : 0 < C * q ^ n / epsilon :=
    div_pos (mul_pos hC hPowPos) hEpsilon
  unfold realGeometricLogarithmicThreshold
  calc
    Real.log (C / epsilon) / (-Real.log q) ≤ (n : ℝ) ↔
        Real.log (C / epsilon) ≤ (n : ℝ) * (-Real.log q) :=
      div_le_iff₀ hDenPos
    _ ↔ Real.log (C * q ^ n / epsilon) ≤ 0 := by
      rw [
        Real.log_div hC.ne' hEpsilon.ne',
        Real.log_div (mul_ne_zero hC.ne' (pow_ne_zero n hqPos.ne')) hEpsilon.ne',
        Real.log_mul hC.ne' (pow_ne_zero n hqPos.ne'),
        Real.log_pow]
      constructor <;> intro h <;> linarith
    _ ↔ C * q ^ n / epsilon ≤ 1 :=
      Real.log_nonpos_iff hQuotPos.le
    _ ↔ C * q ^ n ≤ epsilon := div_le_one hEpsilon

/-- The ceiling count is characterized exactly by the non-strict geometric
stopping inequality. -/
theorem realGeometricCeilingIterationCount_le_iff
    (q C epsilon : ℝ)
    (hqPos : 0 < q)
    (hqLtOne : q < 1)
    (hC : 0 < C)
    (hEpsilon : 0 < epsilon)
    (n : ℕ) :
    realGeometricCeilingIterationCount q C epsilon ≤ n ↔
      C * q ^ n ≤ epsilon := by
  unfold realGeometricCeilingIterationCount
  rw [Nat.ceil_le]
  exact
    realGeometricLogarithmicThreshold_le_nat_iff
      q C epsilon hqPos hqLtOne hC hEpsilon n

/-- At the logarithmic ceiling count itself, the geometric bound holds. -/
theorem realGeometricCeilingIterationCount_spec
    (q C epsilon : ℝ)
    (hqPos : 0 < q)
    (hqLtOne : q < 1)
    (hC : 0 < C)
    (hEpsilon : 0 < epsilon) :
    C * q ^ realGeometricCeilingIterationCount q C epsilon ≤ epsilon :=
  (realGeometricCeilingIterationCount_le_iff
    q C epsilon hqPos hqLtOne hC hEpsilon
    (realGeometricCeilingIterationCount q C epsilon)).1 le_rfl

/-- The logarithmic ceiling is the exact least permanent starting index for the
non-strict geometric stopping predicate. -/
theorem realGeometricCeilingIterationCount_isLeast
    (q C epsilon : ℝ)
    (hqPos : 0 < q)
    (hqLtOne : q < 1)
    (hC : 0 < C)
    (hEpsilon : 0 < epsilon) :
    IsLeast
      {N : ℕ | ∀ n ≥ N, C * q ^ n ≤ epsilon}
      (realGeometricCeilingIterationCount q C epsilon) := by
  constructor
  · intro n hn
    exact
      (realGeometricCeilingIterationCount_le_iff
        q C epsilon hqPos hqLtOne hC hEpsilon n).1 hn
  · intro N hN
    exact
      (realGeometricCeilingIterationCount_le_iff
        q C epsilon hqPos hqLtOne hC hEpsilon N).2
        (hN N le_rfl)

/-- A strict stopping count obtained by doubling the geometric prefactor. Its
closed form is `ceil (log (2 C / epsilon) / (-log q))`. -/
noncomputable def realGeometricStrictCeilingIterationCount
    (q C epsilon : ℝ) : ℕ :=
  realGeometricCeilingIterationCount q (2 * C) epsilon

/-- The doubled-prefactor logarithmic ceiling guarantees the strict geometric
bound `C * q^n < epsilon`. -/
theorem realGeometricStrictCeilingIterationCount_spec
    (q C epsilon : ℝ)
    (hqPos : 0 < q)
    (hqLtOne : q < 1)
    (hC : 0 < C)
    (hEpsilon : 0 < epsilon) :
    ∀ n ≥ realGeometricStrictCeilingIterationCount q C epsilon,
      C * q ^ n < epsilon := by
  intro n hn
  have hTwoC : 0 < 2 * C := mul_pos (by norm_num) hC
  have hBound : (2 * C) * q ^ n ≤ epsilon :=
    (realGeometricCeilingIterationCount_le_iff
      q (2 * C) epsilon hqPos hqLtOne hTwoC hEpsilon n).1 hn
  have hTermNonneg : 0 ≤ C * q ^ n :=
    mul_nonneg hC.le (pow_nonneg hqPos.le n)
  nlinarith

/-- Every permanent strict geometric stopping index is bounded above by the
explicit doubled-prefactor logarithmic ceiling. -/
theorem naturalLeastTailIndex_le_realGeometricStrictCeilingIterationCount
    (q C epsilon : ℝ)
    (hqPos : 0 < q)
    (hqLtOne : q < 1)
    (hC : 0 < C)
    (hEpsilon : 0 < epsilon)
    (hTail : ∃ N : ℕ, naturalTailPredicate (fun n => C * q ^ n < epsilon) N) :
    naturalLeastTailIndex (fun n => C * q ^ n < epsilon) hTail ≤
      realGeometricStrictCeilingIterationCount q C epsilon := by
  apply naturalLeastTailIndex_le
  exact
    realGeometricStrictCeilingIterationCount_spec
      q C epsilon hqPos hqLtOne hC hEpsilon

local notation "E₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2
local notation "q₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2
local notation "Rem₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannRemainderEndL2
local notation "Def₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannInverseDefectEndL2

/-- Exact logarithmic ceiling count for the non-strict Green--Neumann operator
remainder tolerance. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_logarithmicIterationCount
    (epsilon : ℝ) : ℕ :=
  realGeometricCeilingIterationCount q₀ 324 epsilon

/-- The operator-remainder count is literally the requested closed
`log/ceiling` expression with `q_* = 323/325`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_logarithmicIterationCount_eq
    (epsilon : ℝ) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_logarithmicIterationCount epsilon =
      ⌈Real.log ((324 : ℝ) / epsilon) /
        (-Real.log ((323 : ℝ) / 325))⌉₊ := by
  rfl

/-- Exact characterization of every index at or after the operator-remainder
logarithmic ceiling. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_logarithmicIterationCount_le_iff
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon)
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_logarithmicIterationCount epsilon ≤ n ↔
      ‖Rem₀ n‖ ≤ epsilon := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonGreenNeumannRemainderEndL2_eq]
  exact
    realGeometricCeilingIterationCount_le_iff
      q₀ 324 epsilon
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.2
      (by norm_num)
      hEpsilon
      n

/-- The closed logarithmic operator-remainder count is the exact least
permanent non-strict stopping index. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_logarithmicIterationCount_isLeast
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    IsLeast
      {N : ℕ | ∀ n ≥ N, ‖Rem₀ n‖ ≤ epsilon}
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_logarithmicIterationCount epsilon) := by
  constructor
  · intro n hn
    exact
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_logarithmicIterationCount_le_iff
        epsilon hEpsilon n).1 hn
  · intro N hN
    exact
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_logarithmicIterationCount_le_iff
        epsilon hEpsilon N).2
        (hN N le_rfl)

/-- Explicit strict operator-remainder count. Its closed form has numerator
`log (648 / epsilon)`. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_strictLogarithmicIterationCount
    (epsilon : ℝ) : ℕ :=
  realGeometricStrictCeilingIterationCount q₀ 324 epsilon

/-- The explicit strict operator-remainder count guarantees the original strict
stopping predicate from PR #1038. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_norm_lt_of_ge_strictLogarithmicIterationCount
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∀ n ≥ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_strictLogarithmicIterationCount epsilon,
      ‖Rem₀ n‖ < epsilon := by
  intro n hn
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonGreenNeumannRemainderEndL2_eq]
  exact
    realGeometricStrictCeilingIterationCount_spec
      q₀ 324 epsilon
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.2
      (by norm_num)
      hEpsilon
      n hn

/-- The canonical minimal strict operator-remainder index is bounded by the
explicit logarithmic ceiling. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex_le_strictLogarithmicIterationCount
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex
        epsilon hEpsilon ≤
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_strictLogarithmicIterationCount epsilon :=
  (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex_isLeast
    epsilon hEpsilon).2
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_norm_lt_of_ge_strictLogarithmicIterationCount
      epsilon hEpsilon)

/-- Exact logarithmic ceiling count for the non-strict inverse-defect tolerance. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_logarithmicIterationCount
    (epsilon : ℝ) : ℕ :=
  realGeometricCeilingIterationCount q₀ 1 epsilon

/-- The inverse-defect count is the closed expression
`ceil (log (1 / epsilon) / (-log (323/325)))`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_logarithmicIterationCount_eq
    (epsilon : ℝ) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_logarithmicIterationCount epsilon =
      ⌈Real.log ((1 : ℝ) / epsilon) /
        (-Real.log ((323 : ℝ) / 325))⌉₊ := by
  rfl

/-- Exact characterization of the inverse-defect logarithmic count. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_logarithmicIterationCount_le_iff
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon)
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_logarithmicIterationCount epsilon ≤ n ↔
      ‖Def₀ n‖ ≤ epsilon := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonGreenNeumannInverseDefectEndL2_eq]
  simpa only [one_mul] using
    realGeometricCeilingIterationCount_le_iff
      q₀ 1 epsilon
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.2
      (by norm_num)
      hEpsilon
      n

/-- The closed logarithmic inverse-defect count is the exact least permanent
non-strict stopping index. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_logarithmicIterationCount_isLeast
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    IsLeast
      {N : ℕ | ∀ n ≥ N, ‖Def₀ n‖ ≤ epsilon}
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_logarithmicIterationCount epsilon) := by
  constructor
  · intro n hn
    exact
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_logarithmicIterationCount_le_iff
        epsilon hEpsilon n).1 hn
  · intro N hN
    exact
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_logarithmicIterationCount_le_iff
        epsilon hEpsilon N).2
        (hN N le_rfl)

/-- Explicit strict inverse-defect count, with closed numerator
`log (2 / epsilon)`. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_strictLogarithmicIterationCount
    (epsilon : ℝ) : ℕ :=
  realGeometricStrictCeilingIterationCount q₀ 1 epsilon

/-- The strict inverse-defect count guarantees the original strict stopping
predicate. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_norm_lt_of_ge_strictLogarithmicIterationCount
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∀ n ≥ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_strictLogarithmicIterationCount epsilon,
      ‖Def₀ n‖ < epsilon := by
  intro n hn
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonGreenNeumannInverseDefectEndL2_eq]
  simpa only [one_mul] using
    realGeometricStrictCeilingIterationCount_spec
      q₀ 1 epsilon
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.2
      (by norm_num)
      hEpsilon
      n hn

/-- The canonical minimal strict inverse-defect index is bounded by the explicit
logarithmic ceiling. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex_le_strictLogarithmicIterationCount
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex
        epsilon hEpsilon ≤
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_strictLogarithmicIterationCount epsilon :=
  (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex_isLeast
    epsilon hEpsilon).2
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_norm_lt_of_ge_strictLogarithmicIterationCount
      epsilon hEpsilon)

/-- Structured receipt for exact logarithmic and strict ceiling iteration counts
in the actual beta-zero optimal Richardson system. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonLogarithmicIterationCountsL2Receipt :
    Prop where
  generic_exact_ceiling :
    ∀ (q C epsilon : ℝ), 0 < q → q < 1 → 0 < C → 0 < epsilon →
      IsLeast
        {N : ℕ | ∀ n ≥ N, C * q ^ n ≤ epsilon}
        (realGeometricCeilingIterationCount q C epsilon)
  operator_remainder_exact_ceiling :
    ∀ (epsilon : ℝ), 0 < epsilon →
      IsLeast
        {N : ℕ | ∀ n ≥ N, ‖Rem₀ n‖ ≤ epsilon}
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_logarithmicIterationCount epsilon)
  operator_remainder_strict_ceiling :
    ∀ (epsilon : ℝ), 0 < epsilon →
      ∀ n ≥ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_strictLogarithmicIterationCount epsilon,
        ‖Rem₀ n‖ < epsilon
  inverse_defect_exact_ceiling :
    ∀ (epsilon : ℝ), 0 < epsilon →
      IsLeast
        {N : ℕ | ∀ n ≥ N, ‖Def₀ n‖ ≤ epsilon}
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_logarithmicIterationCount epsilon)
  inverse_defect_strict_ceiling :
    ∀ (epsilon : ℝ), 0 < epsilon →
      ∀ n ≥ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_strictLogarithmicIterationCount epsilon,
        ‖Def₀ n‖ < epsilon
  claim_boundary : True

/-- The exact logarithmic iteration-count receipt is inhabited. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonLogarithmicIterationCountsL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonLogarithmicIterationCountsL2Receipt := by
  exact
    { generic_exact_ceiling :=
        realGeometricCeilingIterationCount_isLeast
      operator_remainder_exact_ceiling :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_logarithmicIterationCount_isLeast
      operator_remainder_strict_ceiling :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_norm_lt_of_ge_strictLogarithmicIterationCount
      inverse_defect_exact_ceiling :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_logarithmicIterationCount_isLeast
      inverse_defect_strict_ceiling :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_norm_lt_of_ge_strictLogarithmicIterationCount
      claim_boundary := trivial }

end
end MathlibAnalytic
end MGAP4D
