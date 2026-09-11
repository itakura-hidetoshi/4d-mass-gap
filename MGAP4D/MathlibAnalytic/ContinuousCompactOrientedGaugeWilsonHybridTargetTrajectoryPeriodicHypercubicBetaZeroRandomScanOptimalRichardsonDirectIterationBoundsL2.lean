import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanOptimalRichardsonComplexityRationalEnclosureL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter
open scoped BigOperators Function Topology

noncomputable section

set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 300000

/-- A positive denominator transfers strict bounds on a quotient to strict
multiplicative bounds on its numerator. -/
theorem strict_mul_bounds_of_div_mem_Ioo
    {a b numerator denominator : ℝ}
    (hDenominator : 0 < denominator)
    (hRatio : a < numerator / denominator ∧ numerator / denominator < b) :
    a * denominator < numerator ∧ numerator < b * denominator := by
  constructor
  · exact (lt_div_iff₀ hDenominator).mp hRatio.1
  · exact (div_lt_iff₀ hDenominator).mp hRatio.2

/-- Eventual strict quotient bounds transfer to eventual strict multiplicative
bounds whenever the denominator is eventually positive. -/
theorem eventually_strict_mul_bounds_of_eventually_div_mem_Ioo
    {α : Type*}
    {l : Filter α}
    {f denominator : α → ℝ}
    {a b : ℝ}
    (hDenominator : ∀ᶠ x in l, 0 < denominator x)
    (hRatio : ∀ᶠ x in l, a < f x / denominator x ∧ f x / denominator x < b) :
    ∀ᶠ x in l, a * denominator x < f x ∧ f x < b * denominator x := by
  filter_upwards [hDenominator, hRatio] with x hDenominatorX hRatioX
  exact strict_mul_bounds_of_div_mem_Ioo hDenominatorX hRatioX

/-- The logarithmic denominator is eventually positive as the positive
tolerance tends to zero. -/
theorem realLogOneDiv_eventually_pos_nhdsGT_zero :
    ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ), 0 < Real.log (1 / epsilon) := by
  exact realLogOneDiv_tendsto_atTop_nhdsGT_zero.eventually (eventually_gt_atTop 0)

/-- For sufficiently small positive tolerances, the exact beta-zero
Green--Neumann operator-remainder count is directly bounded between `161` and
`162` times the logarithmic tolerance scale. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_eventually_directBounds_161_162 :
    ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      (161 : ℝ) * Real.log (1 / epsilon) <
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount epsilon : ℝ) ∧
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount epsilon : ℝ) <
          (162 : ℝ) * Real.log (1 / epsilon) := by
  exact eventually_strict_mul_bounds_of_eventually_div_mem_Ioo
    realLogOneDiv_eventually_pos_nhdsGT_zero
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_div_log_oneDiv_eventually_mem_Ioo_161_162

/-- For sufficiently small positive tolerances, the exact beta-zero
Green--Neumann inverse-defect count is directly bounded between `161` and `162`
times the logarithmic tolerance scale. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_eventually_directBounds_161_162 :
    ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      (161 : ℝ) * Real.log (1 / epsilon) <
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount epsilon : ℝ) ∧
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount epsilon : ℝ) <
          (162 : ℝ) * Real.log (1 / epsilon) := by
  exact eventually_strict_mul_bounds_of_eventually_div_mem_Ioo
    realLogOneDiv_eventually_pos_nhdsGT_zero
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_div_log_oneDiv_eventually_mem_Ioo_161_162

/-- The direct operator-remainder bounds transfer pointwise from the exact
closed count to the canonical minimal stopping index. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex_directBounds_161_162
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon)
    (hBounds :
      (161 : ℝ) * Real.log (1 / epsilon) <
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount epsilon : ℝ) ∧
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount epsilon : ℝ) <
          (162 : ℝ) * Real.log (1 / epsilon)) :
    (161 : ℝ) * Real.log (1 / epsilon) <
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex epsilon hEpsilon : ℝ) ∧
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex epsilon hEpsilon : ℝ) <
        (162 : ℝ) * Real.log (1 / epsilon) := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex_eq_exactStrictLogFloorIterationCount
      epsilon hEpsilon]
  exact hBounds

/-- The direct inverse-defect bounds transfer pointwise from the exact closed
count to the canonical minimal stopping index. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex_directBounds_161_162
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon)
    (hBounds :
      (161 : ℝ) * Real.log (1 / epsilon) <
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount epsilon : ℝ) ∧
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount epsilon : ℝ) <
          (162 : ℝ) * Real.log (1 / epsilon)) :
    (161 : ℝ) * Real.log (1 / epsilon) <
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex epsilon hEpsilon : ℝ) ∧
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex epsilon hEpsilon : ℝ) <
        (162 : ℝ) * Real.log (1 / epsilon) := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex_eq_exactStrictLogFloorIterationCount
      epsilon hEpsilon]
  exact hBounds

/-- For sufficiently small positive tolerances, every proof-selected canonical
operator-remainder minimal stopping index satisfies the direct logarithmic
bounds. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex_eventually_directBounds_161_162 :
    ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      ∀ hEpsilon : 0 < epsilon,
        (161 : ℝ) * Real.log (1 / epsilon) <
            (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex epsilon hEpsilon : ℝ) ∧
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex epsilon hEpsilon : ℝ) <
            (162 : ℝ) * Real.log (1 / epsilon) := by
  filter_upwards [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_eventually_directBounds_161_162] with epsilon hBounds
  intro hEpsilon
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex_directBounds_161_162
      epsilon hEpsilon hBounds

/-- For sufficiently small positive tolerances, every proof-selected canonical
inverse-defect minimal stopping index satisfies the direct logarithmic bounds. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex_eventually_directBounds_161_162 :
    ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      ∀ hEpsilon : 0 < epsilon,
        (161 : ℝ) * Real.log (1 / epsilon) <
            (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex epsilon hEpsilon : ℝ) ∧
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex epsilon hEpsilon : ℝ) <
            (162 : ℝ) * Real.log (1 / epsilon) := by
  filter_upwards [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_eventually_directBounds_161_162] with epsilon hBounds
  intro hEpsilon
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex_directBounds_161_162
      epsilon hEpsilon hBounds

/-- Structured receipt for the direct rational logarithmic iteration-count
bounds in the actual finite beta-zero optimal Richardson system. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonDirectIterationBoundsL2Receipt :
    Prop where
  generic_transfer :
    ∀ {α : Type*} {l : Filter α} {f denominator : α → ℝ} {a b : ℝ},
      (∀ᶠ x in l, 0 < denominator x) →
      (∀ᶠ x in l, a < f x / denominator x ∧ f x / denominator x < b) →
      ∀ᶠ x in l, a * denominator x < f x ∧ f x < b * denominator x
  log_denominator_positive :
    ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ), 0 < Real.log (1 / epsilon)
  operator_remainder_exact_direct_bounds :
    ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      (161 : ℝ) * Real.log (1 / epsilon) <
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount epsilon : ℝ) ∧
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount epsilon : ℝ) <
          (162 : ℝ) * Real.log (1 / epsilon)
  inverse_defect_exact_direct_bounds :
    ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      (161 : ℝ) * Real.log (1 / epsilon) <
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount epsilon : ℝ) ∧
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount epsilon : ℝ) <
          (162 : ℝ) * Real.log (1 / epsilon)
  operator_remainder_minimal_direct_bounds :
    ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      ∀ hEpsilon : 0 < epsilon,
        (161 : ℝ) * Real.log (1 / epsilon) <
            (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex epsilon hEpsilon : ℝ) ∧
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex epsilon hEpsilon : ℝ) <
            (162 : ℝ) * Real.log (1 / epsilon)
  inverse_defect_minimal_direct_bounds :
    ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      ∀ hEpsilon : 0 < epsilon,
        (161 : ℝ) * Real.log (1 / epsilon) <
            (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex epsilon hEpsilon : ℝ) ∧
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex epsilon hEpsilon : ℝ) <
            (162 : ℝ) * Real.log (1 / epsilon)
  claim_boundary : True

/-- The direct iteration-bounds receipt is inhabited. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonDirectIterationBoundsL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonDirectIterationBoundsL2Receipt := by
  exact
    { generic_transfer := eventually_strict_mul_bounds_of_eventually_div_mem_Ioo
      log_denominator_positive := realLogOneDiv_eventually_pos_nhdsGT_zero
      operator_remainder_exact_direct_bounds :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_eventually_directBounds_161_162
      inverse_defect_exact_direct_bounds :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_eventually_directBounds_161_162
      operator_remainder_minimal_direct_bounds :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex_eventually_directBounds_161_162
      inverse_defect_minimal_direct_bounds :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex_eventually_directBounds_161_162
      claim_boundary := trivial }

end
end MathlibAnalytic
end MGAP4D
