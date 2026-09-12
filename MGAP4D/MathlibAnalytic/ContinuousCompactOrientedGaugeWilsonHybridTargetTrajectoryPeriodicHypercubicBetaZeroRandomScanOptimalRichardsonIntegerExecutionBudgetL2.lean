import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanOptimalRichardsonDirectIterationBoundsL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter
open scoped BigOperators Function Topology

noncomputable section

set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 300000

/-- Strict real bounds around a natural cast transfer to a closed enclosure by
natural ceilings. -/
theorem natCeil_enclosure_of_strict_natCast_enclosure
    (n : ℕ)
    (lower upper : ℝ)
    (hBounds : lower < (n : ℝ) ∧ (n : ℝ) < upper) :
    ⌈lower⌉₊ ≤ n ∧ n ≤ ⌈upper⌉₊ := by
  constructor
  · exact (Nat.ceil_le).2 hBounds.1.le
  · exact Nat.le_of_lt ((Nat.lt_ceil).2 hBounds.2)

/-- Fully rational lower integer budget associated with the beta-zero
Richardson logarithmic scale. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonLowerExecutionBudgetL2
    (epsilon : ℝ) : ℕ :=
  ⌈(161 : ℝ) * Real.log (1 / epsilon)⌉₊

/-- Fully rational upper integer execution budget associated with the beta-zero
Richardson logarithmic scale. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonUpperExecutionBudgetL2
    (epsilon : ℝ) : ℕ :=
  ⌈(162 : ℝ) * Real.log (1 / epsilon)⌉₊

local notation "B₋" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonLowerExecutionBudgetL2
local notation "B₊" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonUpperExecutionBudgetL2
local notation "Rem₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannRemainderEndL2
local notation "Def₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannInverseDefectEndL2

/-- For sufficiently small positive tolerances, the exact operator-remainder
count lies between the explicit lower and upper natural execution budgets. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_eventually_integerExecutionBudgetBounds :
    ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      B₋ epsilon ≤
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount epsilon ∧
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount epsilon ≤
          B₊ epsilon := by
  filter_upwards [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_eventually_directBounds_161_162] with epsilon hBounds
  simpa only [
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonLowerExecutionBudgetL2,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonUpperExecutionBudgetL2] using
    natCeil_enclosure_of_strict_natCast_enclosure
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount epsilon)
      ((161 : ℝ) * Real.log (1 / epsilon))
      ((162 : ℝ) * Real.log (1 / epsilon))
      hBounds

/-- For sufficiently small positive tolerances, the exact inverse-defect count
lies between the explicit lower and upper natural execution budgets. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_eventually_integerExecutionBudgetBounds :
    ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      B₋ epsilon ≤
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount epsilon ∧
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount epsilon ≤
          B₊ epsilon := by
  filter_upwards [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_eventually_directBounds_161_162] with epsilon hBounds
  simpa only [
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonLowerExecutionBudgetL2,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonUpperExecutionBudgetL2] using
    natCeil_enclosure_of_strict_natCast_enclosure
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount epsilon)
      ((161 : ℝ) * Real.log (1 / epsilon))
      ((162 : ℝ) * Real.log (1 / epsilon))
      hBounds

/-- Every proof-selected canonical operator-remainder minimal stopping index is
eventually enclosed by the explicit natural budgets. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex_eventually_integerExecutionBudgetBounds :
    ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      ∀ hEpsilon : 0 < epsilon,
        B₋ epsilon ≤
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex epsilon hEpsilon ∧
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex epsilon hEpsilon ≤
            B₊ epsilon := by
  filter_upwards [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_eventually_integerExecutionBudgetBounds] with epsilon hBounds
  intro hEpsilon
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex_eq_exactStrictLogFloorIterationCount
      epsilon hEpsilon]
  exact hBounds

/-- Every proof-selected canonical inverse-defect minimal stopping index is
eventually enclosed by the explicit natural budgets. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex_eventually_integerExecutionBudgetBounds :
    ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      ∀ hEpsilon : 0 < epsilon,
        B₋ epsilon ≤
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex epsilon hEpsilon ∧
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex epsilon hEpsilon ≤
            B₊ epsilon := by
  filter_upwards [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_eventually_integerExecutionBudgetBounds] with epsilon hBounds
  intro hEpsilon
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex_eq_exactStrictLogFloorIterationCount
      epsilon hEpsilon]
  exact hBounds

/-- The explicit upper integer budget eventually makes the actual beta-zero
operator remainder strictly smaller than the requested tolerance. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_upperExecutionBudget_norm_lt_eventually :
    ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      ‖Rem₀ (B₊ epsilon)‖ < epsilon := by
  filter_upwards [
    self_mem_nhdsWithin,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_eventually_integerExecutionBudgetBounds] with epsilon hEpsilon hBounds
  have hEpsilonPos : 0 < epsilon := hEpsilon
  exact
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_le_iff
      epsilon hEpsilonPos (B₊ epsilon)).1 hBounds.2

/-- The explicit upper integer budget eventually makes the actual beta-zero
inverse defect strictly smaller than the requested tolerance. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_upperExecutionBudget_norm_lt_eventually :
    ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      ‖Def₀ (B₊ epsilon)‖ < epsilon := by
  filter_upwards [
    self_mem_nhdsWithin,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_eventually_integerExecutionBudgetBounds] with epsilon hEpsilon hBounds
  have hEpsilonPos : 0 < epsilon := hEpsilon
  exact
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_le_iff
      epsilon hEpsilonPos (B₊ epsilon)).1 hBounds.2

/-- Every index at or above the explicit upper integer budget eventually has
operator-remainder norm strictly below the tolerance. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_upperExecutionBudget_permanentTail_eventually :
    ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      ∀ n ≥ B₊ epsilon, ‖Rem₀ n‖ < epsilon := by
  filter_upwards [
    self_mem_nhdsWithin,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_eventually_integerExecutionBudgetBounds] with epsilon hEpsilon hBounds
  have hEpsilonPos : 0 < epsilon := hEpsilon
  intro n hn
  exact
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_le_iff
      epsilon hEpsilonPos n).1
      (hBounds.2.trans hn)

/-- Every index at or above the explicit upper integer budget eventually has
inverse-defect norm strictly below the tolerance. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_upperExecutionBudget_permanentTail_eventually :
    ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      ∀ n ≥ B₊ epsilon, ‖Def₀ n‖ < epsilon := by
  filter_upwards [
    self_mem_nhdsWithin,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_eventually_integerExecutionBudgetBounds] with epsilon hEpsilon hBounds
  have hEpsilonPos : 0 < epsilon := hEpsilon
  intro n hn
  exact
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_le_iff
      epsilon hEpsilonPos n).1
      (hBounds.2.trans hn)

/-- Structured receipt for the executable natural-number iteration budgets and
permanent-tail guarantees in the actual finite beta-zero Richardson system. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonIntegerExecutionBudgetL2Receipt :
    Prop where
  generic_ceiling_transfer :
    ∀ (n : ℕ) (lower upper : ℝ),
      lower < (n : ℝ) ∧ (n : ℝ) < upper →
        ⌈lower⌉₊ ≤ n ∧ n ≤ ⌈upper⌉₊
  operator_remainder_exact_budget_bounds :
    ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      B₋ epsilon ≤
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount epsilon ∧
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount epsilon ≤
          B₊ epsilon
  inverse_defect_exact_budget_bounds :
    ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      B₋ epsilon ≤
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount epsilon ∧
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount epsilon ≤
          B₊ epsilon
  operator_remainder_minimal_budget_bounds :
    ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      ∀ hEpsilon : 0 < epsilon,
        B₋ epsilon ≤
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex epsilon hEpsilon ∧
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex epsilon hEpsilon ≤
            B₊ epsilon
  inverse_defect_minimal_budget_bounds :
    ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      ∀ hEpsilon : 0 < epsilon,
        B₋ epsilon ≤
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex epsilon hEpsilon ∧
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex epsilon hEpsilon ≤
            B₊ epsilon
  operator_remainder_upper_budget_tail :
    ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      ∀ n ≥ B₊ epsilon, ‖Rem₀ n‖ < epsilon
  inverse_defect_upper_budget_tail :
    ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      ∀ n ≥ B₊ epsilon, ‖Def₀ n‖ < epsilon
  claim_boundary : True

/-- The integer execution-budget receipt is inhabited. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonIntegerExecutionBudgetL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonIntegerExecutionBudgetL2Receipt := by
  exact
    { generic_ceiling_transfer := natCeil_enclosure_of_strict_natCast_enclosure
      operator_remainder_exact_budget_bounds :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_eventually_integerExecutionBudgetBounds
      inverse_defect_exact_budget_bounds :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_eventually_integerExecutionBudgetBounds
      operator_remainder_minimal_budget_bounds :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex_eventually_integerExecutionBudgetBounds
      inverse_defect_minimal_budget_bounds :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex_eventually_integerExecutionBudgetBounds
      operator_remainder_upper_budget_tail :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_upperExecutionBudget_permanentTail_eventually
      inverse_defect_upper_budget_tail :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_upperExecutionBudget_permanentTail_eventually
      claim_boundary := trivial }

end
end MathlibAnalytic
end MGAP4D
