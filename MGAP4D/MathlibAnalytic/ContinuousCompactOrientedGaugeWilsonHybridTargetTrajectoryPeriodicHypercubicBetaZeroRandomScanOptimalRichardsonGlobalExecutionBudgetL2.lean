import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanOptimalRichardsonIntegerExecutionBudgetL2
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanOptimalRichardsonStoppingCountMonotonicityRoundingL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter
open scoped BigOperators Function Topology

noncomputable section

set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 300000

/-- A global natural-number budget for a strict geometric stopping problem.  If
`epsilon` already exceeds the initial prefactor `C`, no iteration is needed;
otherwise the budget is the natural ceiling of a logarithmic upper estimate. -/
noncomputable def realGeometricGlobalStrictExecutionBudget
    (K C epsilon : ℝ) : ℕ :=
  if C < epsilon then 0 else
    ⌈K * Real.log (C / epsilon) + 1⌉₊

/-- A coefficient strictly larger than the exact logarithmic complexity
constant gives a global upper bound for the exact strict geometric stopping
count, for every positive tolerance. -/
theorem realGeometricExactStrictLogFloorIterationCount_le_globalStrictExecutionBudget
    (q K C epsilon : ℝ)
    (hqPos : 0 < q)
    (hqLtOne : q < 1)
    (hC : 0 < C)
    (hEpsilon : 0 < epsilon)
    (hK : 1 / (-Real.log q) < K) :
    realGeometricExactStrictLogFloorIterationCount q C epsilon ≤
      realGeometricGlobalStrictExecutionBudget K C epsilon := by
  by_cases hInitial : C < epsilon
  · have hCountZero :
        realGeometricExactStrictLogFloorIterationCount q C epsilon = 0 :=
      (realGeometricExactStrictLogFloorIterationCount_eq_zero_iff
        q C epsilon hqPos hqLtOne hC hEpsilon).2 hInitial
    simp [realGeometricGlobalStrictExecutionBudget, hInitial, hCountZero]
  · have hEpsilonLeC : epsilon ≤ C := le_of_not_gt hInitial
    by_cases hEqual : epsilon = C
    · subst epsilon
      simp [realGeometricGlobalStrictExecutionBudget,
        realGeometricExactStrictLogFloorIterationCount,
        realGeometricLogarithmicThreshold, hC.ne']
    · have hEpsilonLtC : epsilon < C :=
        lt_of_le_of_ne hEpsilonLeC hEqual
      have hRatio : (1 : ℝ) < C / epsilon :=
        (one_lt_div hEpsilon).2 hEpsilonLtC
      have hLogPos : 0 < Real.log (C / epsilon) :=
        Real.log_pos hRatio
      have hThresholdLt :
          realGeometricLogarithmicThreshold q C epsilon <
            K * Real.log (C / epsilon) := by
        unfold realGeometricLogarithmicThreshold
        calc
          Real.log (C / epsilon) / (-Real.log q) =
              Real.log (C / epsilon) * (1 / (-Real.log q)) := by ring
          _ < Real.log (C / epsilon) * K :=
            mul_lt_mul_of_pos_left hK hLogPos
          _ = K * Real.log (C / epsilon) := by ring
      have hCountLe :
          (realGeometricExactStrictLogFloorIterationCount q C epsilon : ℝ) ≤
            realGeometricLogarithmicThreshold q C epsilon + 1 :=
        realGeometricExactStrictLogFloorIterationCount_le_threshold_add_one
          q C epsilon hqPos hqLtOne hC hEpsilon hEpsilonLeC
      have hCountLt :
          (realGeometricExactStrictLogFloorIterationCount q C epsilon : ℝ) <
            K * Real.log (C / epsilon) + 1 :=
        lt_of_le_of_lt hCountLe (add_lt_add_right hThresholdLt 1)
      have hNatLt :
          realGeometricExactStrictLogFloorIterationCount q C epsilon <
            ⌈K * Real.log (C / epsilon) + 1⌉₊ :=
        (Nat.lt_ceil).2 hCountLt
      have hNatLe :
          realGeometricExactStrictLogFloorIterationCount q C epsilon ≤
            ⌈K * Real.log (C / epsilon) + 1⌉₊ :=
        Nat.le_of_lt hNatLt
      simpa [realGeometricGlobalStrictExecutionBudget, hInitial] using hNatLe

/-- Every index at or above the global budget satisfies the strict geometric
error target. -/
theorem realGeometricGlobalStrictExecutionBudget_permanentTail
    (q K C epsilon : ℝ)
    (hqPos : 0 < q)
    (hqLtOne : q < 1)
    (hC : 0 < C)
    (hEpsilon : 0 < epsilon)
    (hK : 1 / (-Real.log q) < K) :
    ∀ n ≥ realGeometricGlobalStrictExecutionBudget K C epsilon,
      C * q ^ n < epsilon := by
  intro n hn
  exact
    (realGeometricExactStrictLogFloorIterationCount_le_iff
      q C epsilon hqPos hqLtOne hC hEpsilon n).1
      ((realGeometricExactStrictLogFloorIterationCount_le_globalStrictExecutionBudget
        q K C epsilon hqPos hqLtOne hC hEpsilon hK).trans hn)

/-- In particular, the global budget itself satisfies the strict geometric
error target. -/
theorem realGeometricGlobalStrictExecutionBudget_spec
    (q K C epsilon : ℝ)
    (hqPos : 0 < q)
    (hqLtOne : q < 1)
    (hC : 0 < C)
    (hEpsilon : 0 < epsilon)
    (hK : 1 / (-Real.log q) < K) :
    C * q ^ realGeometricGlobalStrictExecutionBudget K C epsilon < epsilon :=
  realGeometricGlobalStrictExecutionBudget_permanentTail
    q K C epsilon hqPos hqLtOne hC hEpsilon hK
    (realGeometricGlobalStrictExecutionBudget K C epsilon) le_rfl

local notation "q₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2
local notation "Rem₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannRemainderEndL2
local notation "Def₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannInverseDefectEndL2

/-- Global all-tolerance execution budget for the actual beta-zero
Green--Neumann operator remainder. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannRemainderEndL2GlobalExecutionBudget
    (epsilon : ℝ) : ℕ :=
  realGeometricGlobalStrictExecutionBudget 162 324 epsilon

/-- Global all-tolerance execution budget for the actual beta-zero
Green--Neumann inverse defect. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannInverseDefectEndL2GlobalExecutionBudget
    (epsilon : ℝ) : ℕ :=
  realGeometricGlobalStrictExecutionBudget 162 1 epsilon

local notation "BRem" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannRemainderEndL2GlobalExecutionBudget
local notation "BDef" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannInverseDefectEndL2GlobalExecutionBudget

/-- Closed piecewise formula for the global operator-remainder budget. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannRemainderEndL2GlobalExecutionBudget_eq
    (epsilon : ℝ) :
    BRem epsilon =
      if (324 : ℝ) < epsilon then 0 else
        ⌈(162 : ℝ) * Real.log ((324 : ℝ) / epsilon) + 1⌉₊ := by
  rfl

/-- Closed piecewise formula for the global inverse-defect budget. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannInverseDefectEndL2GlobalExecutionBudget_eq
    (epsilon : ℝ) :
    BDef epsilon =
      if (1 : ℝ) < epsilon then 0 else
        ⌈(162 : ℝ) * Real.log ((1 : ℝ) / epsilon) + 1⌉₊ := by
  rfl

private theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardson_logarithmicComplexityCoefficient_lt_162 :
    1 / (-Real.log q₀) < (162 : ℝ) := by
  change 1 / (-Real.log ((323 : ℝ) / 325)) < (162 : ℝ)
  exact
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardson_logarithmicComplexityConstant_lt_162

/-- For every positive tolerance, the exact operator-remainder stopping count is
at most the global piecewise natural budget. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_le_globalExecutionBudget
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount epsilon ≤
      BRem epsilon := by
  change realGeometricExactStrictLogFloorIterationCount q₀ 324 epsilon ≤
    realGeometricGlobalStrictExecutionBudget 162 324 epsilon
  exact
    realGeometricExactStrictLogFloorIterationCount_le_globalStrictExecutionBudget
      q₀ 162 324 epsilon
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.2
      (by norm_num) hEpsilon
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardson_logarithmicComplexityCoefficient_lt_162

/-- For every positive tolerance, the exact inverse-defect stopping count is at
most the global piecewise natural budget. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_le_globalExecutionBudget
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount epsilon ≤
      BDef epsilon := by
  change realGeometricExactStrictLogFloorIterationCount q₀ 1 epsilon ≤
    realGeometricGlobalStrictExecutionBudget 162 1 epsilon
  exact
    realGeometricExactStrictLogFloorIterationCount_le_globalStrictExecutionBudget
      q₀ 162 1 epsilon
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.2
      (by norm_num) hEpsilon
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardson_logarithmicComplexityCoefficient_lt_162

/-- Every proof-selected canonical operator-remainder minimal stopping index is
bounded by the global piecewise natural budget for every positive tolerance. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex_le_globalExecutionBudget
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex epsilon hEpsilon ≤
      BRem epsilon := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex_eq_exactStrictLogFloorIterationCount
      epsilon hEpsilon]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_le_globalExecutionBudget
      epsilon hEpsilon

/-- Every proof-selected canonical inverse-defect minimal stopping index is
bounded by the global piecewise natural budget for every positive tolerance. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex_le_globalExecutionBudget
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex epsilon hEpsilon ≤
      BDef epsilon := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex_eq_exactStrictLogFloorIterationCount
      epsilon hEpsilon]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_le_globalExecutionBudget
      epsilon hEpsilon

/-- The global operator-remainder budget itself meets the requested tolerance
for every positive tolerance. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_globalExecutionBudget_norm_lt
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ‖Rem₀ (BRem epsilon)‖ < epsilon :=
  (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_le_iff
    epsilon hEpsilon (BRem epsilon)).1
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_le_globalExecutionBudget
      epsilon hEpsilon)

/-- The global inverse-defect budget itself meets the requested tolerance for
every positive tolerance. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_globalExecutionBudget_norm_lt
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ‖Def₀ (BDef epsilon)‖ < epsilon :=
  (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_le_iff
    epsilon hEpsilon (BDef epsilon)).1
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_le_globalExecutionBudget
      epsilon hEpsilon)

/-- Every index at or above the global operator-remainder budget permanently
meets the requested tolerance. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_globalExecutionBudget_permanentTail
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∀ n ≥ BRem epsilon, ‖Rem₀ n‖ < epsilon := by
  intro n hn
  exact
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_le_iff
      epsilon hEpsilon n).1
      ((periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_le_globalExecutionBudget
        epsilon hEpsilon).trans hn)

/-- Every index at or above the global inverse-defect budget permanently meets
the requested tolerance. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_globalExecutionBudget_permanentTail
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∀ n ≥ BDef epsilon, ‖Def₀ n‖ < epsilon := by
  intro n hn
  exact
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_le_iff
      epsilon hEpsilon n).1
      ((periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_le_globalExecutionBudget
        epsilon hEpsilon).trans hn)

/-- Structured receipt for global, non-asymptotic, all-positive-tolerance
execution budgets in the actual finite beta-zero Richardson system. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGlobalExecutionBudgetL2Receipt :
    Prop where
  generic_global_upper :
    ∀ (q K C epsilon : ℝ), 0 < q → q < 1 → 0 < C → 0 < epsilon →
      1 / (-Real.log q) < K →
      realGeometricExactStrictLogFloorIterationCount q C epsilon ≤
        realGeometricGlobalStrictExecutionBudget K C epsilon
  generic_permanent_tail :
    ∀ (q K C epsilon : ℝ), 0 < q → q < 1 → 0 < C → 0 < epsilon →
      1 / (-Real.log q) < K →
      ∀ n ≥ realGeometricGlobalStrictExecutionBudget K C epsilon,
        C * q ^ n < epsilon
  operator_remainder_exact_upper :
    ∀ (epsilon : ℝ), 0 < epsilon →
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount epsilon ≤
        BRem epsilon
  inverse_defect_exact_upper :
    ∀ (epsilon : ℝ), 0 < epsilon →
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount epsilon ≤
        BDef epsilon
  operator_remainder_minimal_upper :
    ∀ (epsilon : ℝ) (hEpsilon : 0 < epsilon),
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex epsilon hEpsilon ≤
        BRem epsilon
  inverse_defect_minimal_upper :
    ∀ (epsilon : ℝ) (hEpsilon : 0 < epsilon),
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex epsilon hEpsilon ≤
        BDef epsilon
  operator_remainder_permanent_tail :
    ∀ (epsilon : ℝ), 0 < epsilon →
      ∀ n ≥ BRem epsilon, ‖Rem₀ n‖ < epsilon
  inverse_defect_permanent_tail :
    ∀ (epsilon : ℝ), 0 < epsilon →
      ∀ n ≥ BDef epsilon, ‖Def₀ n‖ < epsilon
  claim_boundary : True

/-- The global execution-budget receipt is inhabited. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGlobalExecutionBudgetL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGlobalExecutionBudgetL2Receipt := by
  exact
    { generic_global_upper :=
        realGeometricExactStrictLogFloorIterationCount_le_globalStrictExecutionBudget
      generic_permanent_tail :=
        realGeometricGlobalStrictExecutionBudget_permanentTail
      operator_remainder_exact_upper :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_le_globalExecutionBudget
      inverse_defect_exact_upper :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_le_globalExecutionBudget
      operator_remainder_minimal_upper :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex_le_globalExecutionBudget
      inverse_defect_minimal_upper :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex_le_globalExecutionBudget
      operator_remainder_permanent_tail :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_globalExecutionBudget_permanentTail
      inverse_defect_permanent_tail :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_globalExecutionBudget_permanentTail
      claim_boundary := trivial }

end
end MathlibAnalytic
end MGAP4D
