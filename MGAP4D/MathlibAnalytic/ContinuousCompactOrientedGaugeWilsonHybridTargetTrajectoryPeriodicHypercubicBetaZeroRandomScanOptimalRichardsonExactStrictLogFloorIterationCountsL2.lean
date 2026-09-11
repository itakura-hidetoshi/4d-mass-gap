import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanOptimalRichardsonLogarithmicIterationCountsL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000

/-- For positive geometric data and `0 < q < 1`, the strict logarithmic
threshold inequality is exactly equivalent to the strict geometric bound. -/
theorem realGeometricLogarithmicThreshold_lt_nat_iff
    (q C epsilon : ℝ)
    (hqPos : 0 < q)
    (hqLtOne : q < 1)
    (hC : 0 < C)
    (hEpsilon : 0 < epsilon)
    (n : ℕ) :
    realGeometricLogarithmicThreshold q C epsilon < (n : ℝ) ↔
      C * q ^ n < epsilon := by
  have hLogNeg : Real.log q < 0 :=
    Real.log_neg hqPos hqLtOne
  have hDenPos : 0 < -Real.log q := neg_pos.mpr hLogNeg
  have hPowPos : 0 < q ^ n := pow_pos hqPos n
  have hQuotPos : 0 < C * q ^ n / epsilon :=
    div_pos (mul_pos hC hPowPos) hEpsilon
  unfold realGeometricLogarithmicThreshold
  calc
    Real.log (C / epsilon) / (-Real.log q) < (n : ℝ) ↔
        Real.log (C / epsilon) < (n : ℝ) * (-Real.log q) :=
      div_lt_iff₀ hDenPos
    _ ↔ Real.log (C * q ^ n / epsilon) < 0 := by
      rw [
        Real.log_div hC.ne' hEpsilon.ne',
        Real.log_div (mul_ne_zero hC.ne' (pow_ne_zero n hqPos.ne')) hEpsilon.ne',
        Real.log_mul hC.ne' (pow_ne_zero n hqPos.ne'),
        Real.log_pow]
      constructor <;> intro h <;> linarith
    _ ↔ C * q ^ n / epsilon < 1 :=
      Real.log_neg_iff hQuotPos
    _ ↔ C * q ^ n < epsilon := div_lt_one hEpsilon

/-- The exact natural starting index for the strict geometric inequality
`C * q^n < epsilon`. If the inequality already holds at `n = 0`, the count is
zero; otherwise it is one more than the natural floor of the logarithmic
threshold. -/
noncomputable def realGeometricExactStrictLogFloorIterationCount
    (q C epsilon : ℝ) : ℕ :=
  if C < epsilon then 0 else
    ⌊realGeometricLogarithmicThreshold q C epsilon⌋₊ + 1

/-- Exact characterization of the strict log-floor count. -/
theorem realGeometricExactStrictLogFloorIterationCount_le_iff
    (q C epsilon : ℝ)
    (hqPos : 0 < q)
    (hqLtOne : q < 1)
    (hC : 0 < C)
    (hEpsilon : 0 < epsilon)
    (n : ℕ) :
    realGeometricExactStrictLogFloorIterationCount q C epsilon ≤ n ↔
      C * q ^ n < epsilon := by
  rw [← realGeometricLogarithmicThreshold_lt_nat_iff
    q C epsilon hqPos hqLtOne hC hEpsilon n]
  by_cases hInitial : C < epsilon
  · have hThresholdLtZero :
        realGeometricLogarithmicThreshold q C epsilon < (0 : ℝ) := by
      simpa using
        (realGeometricLogarithmicThreshold_lt_nat_iff
          q C epsilon hqPos hqLtOne hC hEpsilon 0).2
          (by simpa using hInitial)
    simp only [realGeometricExactStrictLogFloorIterationCount, hInitial, if_pos,
      Nat.zero_le, true_iff]
    exact hThresholdLtZero.trans_le (Nat.cast_nonneg n)
  · have hThresholdNonneg :
        0 ≤ realGeometricLogarithmicThreshold q C epsilon := by
      apply le_of_not_gt
      intro hThresholdLtZero
      apply hInitial
      have h :=
        (realGeometricLogarithmicThreshold_lt_nat_iff
          q C epsilon hqPos hqLtOne hC hEpsilon 0).1
          (by simpa using hThresholdLtZero)
      simpa using h
    simp only [realGeometricExactStrictLogFloorIterationCount, hInitial, if_false]
    constructor
    · intro hCount
      have hFloorLt :
          ⌊realGeometricLogarithmicThreshold q C epsilon⌋₊ < n := by
        omega
      exact (Nat.floor_lt hThresholdNonneg).1 hFloorLt
    · intro hThresholdLt
      have hFloorLt :
          ⌊realGeometricLogarithmicThreshold q C epsilon⌋₊ < n :=
        (Nat.floor_lt hThresholdNonneg).2 hThresholdLt
      omega

/-- The strict geometric inequality holds at the exact log-floor count. -/
theorem realGeometricExactStrictLogFloorIterationCount_spec
    (q C epsilon : ℝ)
    (hqPos : 0 < q)
    (hqLtOne : q < 1)
    (hC : 0 < C)
    (hEpsilon : 0 < epsilon) :
    C * q ^ realGeometricExactStrictLogFloorIterationCount q C epsilon < epsilon :=
  (realGeometricExactStrictLogFloorIterationCount_le_iff
    q C epsilon hqPos hqLtOne hC hEpsilon
    (realGeometricExactStrictLogFloorIterationCount q C epsilon)).1 le_rfl

/-- The strict log-floor count is the exact least permanent starting index for
`C * q^n < epsilon`. -/
theorem realGeometricExactStrictLogFloorIterationCount_isLeast
    (q C epsilon : ℝ)
    (hqPos : 0 < q)
    (hqLtOne : q < 1)
    (hC : 0 < C)
    (hEpsilon : 0 < epsilon) :
    IsLeast
      {N : ℕ | ∀ n ≥ N, C * q ^ n < epsilon}
      (realGeometricExactStrictLogFloorIterationCount q C epsilon) := by
  constructor
  · intro n hn
    exact
      (realGeometricExactStrictLogFloorIterationCount_le_iff
        q C epsilon hqPos hqLtOne hC hEpsilon n).1 hn
  · intro N hN
    exact
      (realGeometricExactStrictLogFloorIterationCount_le_iff
        q C epsilon hqPos hqLtOne hC hEpsilon N).2
        (hN N le_rfl)

/-- The canonical well-ordering construction of the least strict tail index is
identical to the exact log-floor closed form. -/
theorem naturalLeastTailIndex_eq_realGeometricExactStrictLogFloorIterationCount
    (q C epsilon : ℝ)
    (hqPos : 0 < q)
    (hqLtOne : q < 1)
    (hC : 0 < C)
    (hEpsilon : 0 < epsilon)
    (hTail : ∃ N : ℕ,
      naturalTailPredicate (fun n => C * q ^ n < epsilon) N) :
    naturalLeastTailIndex (fun n => C * q ^ n < epsilon) hTail =
      realGeometricExactStrictLogFloorIterationCount q C epsilon := by
  have hNaturalLeast :
      IsLeast
        {N : ℕ | ∀ n ≥ N, C * q ^ n < epsilon}
        (naturalLeastTailIndex (fun n => C * q ^ n < epsilon) hTail) := by
    simpa only [naturalTailPredicate] using
      naturalLeastTailIndex_isLeast (fun n => C * q ^ n < epsilon) hTail
  have hClosedLeast :=
    realGeometricExactStrictLogFloorIterationCount_isLeast
      q C epsilon hqPos hqLtOne hC hEpsilon
  exact le_antisymm (hNaturalLeast.2 hClosedLeast.1)
    (hClosedLeast.2 hNaturalLeast.1)

/-- The exact strict log-floor count is never larger than the earlier doubled-
prefactor strict ceiling count. -/
theorem realGeometricExactStrictLogFloorIterationCount_le_strictCeilingIterationCount
    (q C epsilon : ℝ)
    (hqPos : 0 < q)
    (hqLtOne : q < 1)
    (hC : 0 < C)
    (hEpsilon : 0 < epsilon) :
    realGeometricExactStrictLogFloorIterationCount q C epsilon ≤
      realGeometricStrictCeilingIterationCount q C epsilon :=
  (realGeometricExactStrictLogFloorIterationCount_isLeast
    q C epsilon hqPos hqLtOne hC hEpsilon).2
    (realGeometricStrictCeilingIterationCount_spec
      q C epsilon hqPos hqLtOne hC hEpsilon)

local notation "q₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2
local notation "Rem₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannRemainderEndL2
local notation "Def₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannInverseDefectEndL2

/-- Exact strict log-floor count for the Green--Neumann operator remainder. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount
    (epsilon : ℝ) : ℕ :=
  realGeometricExactStrictLogFloorIterationCount q₀ 324 epsilon

/-- Closed piecewise floor/log formula for the exact strict operator-remainder
count. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_eq
    (epsilon : ℝ) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount epsilon =
      if (324 : ℝ) < epsilon then 0 else
        ⌊Real.log ((324 : ℝ) / epsilon) /
          (-Real.log ((323 : ℝ) / 325))⌋₊ + 1 := by
  rfl

/-- Exact characterization of every index at or after the strict
operator-remainder log-floor count. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_le_iff
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon)
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount epsilon ≤ n ↔
      ‖Rem₀ n‖ < epsilon := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonGreenNeumannRemainderEndL2_eq]
  exact
    realGeometricExactStrictLogFloorIterationCount_le_iff
      q₀ 324 epsilon
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.2
      (by norm_num)
      hEpsilon
      n

/-- The exact strict operator-remainder count is the least permanent strict
stopping index. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_isLeast
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    IsLeast
      {N : ℕ | ∀ n ≥ N, ‖Rem₀ n‖ < epsilon}
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount epsilon) := by
  constructor
  · intro n hn
    exact
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_le_iff
        epsilon hEpsilon n).1 hn
  · intro N hN
    exact
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_le_iff
        epsilon hEpsilon N).2
        (hN N le_rfl)

/-- The canonical minimal strict operator-remainder stopping index is exactly
the closed log-floor count. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex_eq_exactStrictLogFloorIterationCount
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex
        epsilon hEpsilon =
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount epsilon := by
  have hMinimal :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex_isLeast
      epsilon hEpsilon
  have hClosed :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_isLeast
      epsilon hEpsilon
  exact le_antisymm (hMinimal.2 hClosed.1) (hClosed.2 hMinimal.1)

/-- The exact strict operator-remainder count improves the previous explicit
strict ceiling bound. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_le_strictLogarithmicIterationCount
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount epsilon ≤
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_strictLogarithmicIterationCount epsilon :=
  (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_isLeast
    epsilon hEpsilon).2
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_norm_lt_of_ge_strictLogarithmicIterationCount
      epsilon hEpsilon)

/-- Exact strict log-floor count for the Green--Neumann inverse defect. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount
    (epsilon : ℝ) : ℕ :=
  realGeometricExactStrictLogFloorIterationCount q₀ 1 epsilon

/-- Closed piecewise floor/log formula for the exact strict inverse-defect
count. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_eq
    (epsilon : ℝ) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount epsilon =
      if (1 : ℝ) < epsilon then 0 else
        ⌊Real.log ((1 : ℝ) / epsilon) /
          (-Real.log ((323 : ℝ) / 325))⌋₊ + 1 := by
  rfl

/-- Exact characterization of every index at or after the strict inverse-defect
log-floor count. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_le_iff
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon)
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount epsilon ≤ n ↔
      ‖Def₀ n‖ < epsilon := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonGreenNeumannInverseDefectEndL2_eq]
  simpa only [one_mul] using
    realGeometricExactStrictLogFloorIterationCount_le_iff
      q₀ 1 epsilon
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.2
      (by norm_num)
      hEpsilon
      n

/-- The exact strict inverse-defect count is the least permanent strict stopping
index. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_isLeast
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    IsLeast
      {N : ℕ | ∀ n ≥ N, ‖Def₀ n‖ < epsilon}
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount epsilon) := by
  constructor
  · intro n hn
    exact
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_le_iff
        epsilon hEpsilon n).1 hn
  · intro N hN
    exact
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_le_iff
        epsilon hEpsilon N).2
        (hN N le_rfl)

/-- The canonical minimal strict inverse-defect stopping index is exactly the
closed log-floor count. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex_eq_exactStrictLogFloorIterationCount
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex
        epsilon hEpsilon =
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount epsilon := by
  have hMinimal :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex_isLeast
      epsilon hEpsilon
  have hClosed :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_isLeast
      epsilon hEpsilon
  exact le_antisymm (hMinimal.2 hClosed.1) (hClosed.2 hMinimal.1)

/-- The exact strict inverse-defect count improves the previous explicit strict
ceiling bound. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_le_strictLogarithmicIterationCount
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount epsilon ≤
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_strictLogarithmicIterationCount epsilon :=
  (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_isLeast
    epsilon hEpsilon).2
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_norm_lt_of_ge_strictLogarithmicIterationCount
      epsilon hEpsilon)

/-- Structured receipt for exact strict log-floor iteration counts in the actual
finite beta-zero optimal Richardson system. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonExactStrictLogFloorIterationCountsL2Receipt :
    Prop where
  generic_exact_strict :
    ∀ (q C epsilon : ℝ), 0 < q → q < 1 → 0 < C → 0 < epsilon →
      IsLeast
        {N : ℕ | ∀ n ≥ N, C * q ^ n < epsilon}
        (realGeometricExactStrictLogFloorIterationCount q C epsilon)
  operator_remainder_exact :
    ∀ (epsilon : ℝ) (hEpsilon : 0 < epsilon),
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex
          epsilon hEpsilon =
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount epsilon
  inverse_defect_exact :
    ∀ (epsilon : ℝ) (hEpsilon : 0 < epsilon),
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex
          epsilon hEpsilon =
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount epsilon
  operator_remainder_improves_ceiling :
    ∀ (epsilon : ℝ) (hEpsilon : 0 < epsilon),
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount epsilon ≤
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_strictLogarithmicIterationCount epsilon
  inverse_defect_improves_ceiling :
    ∀ (epsilon : ℝ) (hEpsilon : 0 < epsilon),
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount epsilon ≤
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_strictLogarithmicIterationCount epsilon
  claim_boundary : True

/-- The exact strict log-floor receipt is inhabited. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonExactStrictLogFloorIterationCountsL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonExactStrictLogFloorIterationCountsL2Receipt := by
  exact
    { generic_exact_strict :=
        realGeometricExactStrictLogFloorIterationCount_isLeast
      operator_remainder_exact :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex_eq_exactStrictLogFloorIterationCount
      inverse_defect_exact :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex_eq_exactStrictLogFloorIterationCount
      operator_remainder_improves_ceiling :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_le_strictLogarithmicIterationCount
      inverse_defect_improves_ceiling :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_le_strictLogarithmicIterationCount
      claim_boundary := trivial }

end
end MathlibAnalytic
end MGAP4D
