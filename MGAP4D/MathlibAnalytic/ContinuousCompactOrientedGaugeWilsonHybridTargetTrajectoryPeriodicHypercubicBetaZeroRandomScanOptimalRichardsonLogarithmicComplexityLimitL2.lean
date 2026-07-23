import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanOptimalRichardsonStoppingCountMonotonicityRoundingL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter
open scoped BigOperators Function Topology

noncomputable section

set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 300000

/-- The logarithmic denominator `log (1 / epsilon)` tends to positive infinity
as the positive tolerance tends to zero. -/
theorem realLogOneDiv_tendsto_atTop_nhdsGT_zero :
    Tendsto (fun epsilon : ℝ => Real.log (1 / epsilon)) (𝓝[>] (0 : ℝ)) atTop := by
  simpa only [one_div] using
    Real.tendsto_log_atTop.comp
      (tendsto_inv_nhdsGT_zero :
        Tendsto (fun epsilon : ℝ => epsilon⁻¹) (𝓝[>] (0 : ℝ)) atTop)

/-- Along exponentially small tolerances `epsilon = exp (-x)`, the exact
strict stopping count divided by `x` converges to the reciprocal logarithmic
contraction rate. -/
theorem realGeometricExactStrictLogFloorIterationCount_exp_neg_div_tendsto
    (q C : ℝ)
    (hqPos : 0 < q)
    (hqLtOne : q < 1)
    (hC : 0 < C) :
    Tendsto
      (fun x : ℝ =>
        (realGeometricExactStrictLogFloorIterationCount q C (Real.exp (-x)) : ℝ) / x)
      atTop
      (𝓝 (1 / (-Real.log q))) := by
  have hLogNeg : Real.log q < 0 := Real.log_neg hqPos hqLtOne
  have hDenPos : 0 < -Real.log q := neg_pos.mpr hLogNeg
  have hDenNe : -Real.log q ≠ 0 := hDenPos.ne'
  have hExpLe : ∀ᶠ x : ℝ in atTop, Real.exp (-x) ≤ C :=
    Real.tendsto_exp_neg_atTop_nhds_zero.eventually (Iic_mem_nhds hC)
  have hThresholdRatio :
      Tendsto
        (fun x : ℝ =>
          realGeometricLogarithmicThreshold q C (Real.exp (-x)) / x)
        atTop
        (𝓝 (1 / (-Real.log q))) := by
    have hConstOver :
        Tendsto
          (fun x : ℝ => (Real.log C / (-Real.log q)) / x)
          atTop
          (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have hModel :
        Tendsto
          (fun x : ℝ =>
            1 / (-Real.log q) + (Real.log C / (-Real.log q)) / x)
          atTop
          (𝓝 (1 / (-Real.log q))) := by
      simpa only [add_zero] using tendsto_const_nhds.add hConstOver
    refine hModel.congr' ?_
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
    unfold realGeometricLogarithmicThreshold
    rw [Real.log_div hC.ne' (Real.exp_ne_zero _), Real.log_exp]
    field_simp [hx, hDenNe]
    ring
  have hRoundDiv :
      Tendsto
        (fun x : ℝ =>
          ((realGeometricExactStrictLogFloorIterationCount q C (Real.exp (-x)) : ℝ) -
              realGeometricLogarithmicThreshold q C (Real.exp (-x))) / x)
        atTop
        (𝓝 0) := by
    have hBound :
        ∀ᶠ x : ℝ in atTop,
          ‖((realGeometricExactStrictLogFloorIterationCount q C (Real.exp (-x)) : ℝ) -
                realGeometricLogarithmicThreshold q C (Real.exp (-x))) / x‖ ≤
            (1 : ℝ) / x := by
      filter_upwards [hExpLe, eventually_gt_atTop (0 : ℝ)] with x hxC hx
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hx]
      exact div_le_div_of_nonneg_right
        (realGeometricExactStrictLogFloorIterationCount_abs_sub_threshold_le_one
          q C (Real.exp (-x)) hqPos hqLtOne hC (Real.exp_pos _) hxC)
        hx.le
    have hOneDiv :
        Tendsto (fun x : ℝ => (1 : ℝ) / x) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    exact squeeze_zero_norm' hBound hOneDiv
  have hSum :
      Tendsto
        (fun x : ℝ =>
          realGeometricLogarithmicThreshold q C (Real.exp (-x)) / x +
            ((realGeometricExactStrictLogFloorIterationCount q C (Real.exp (-x)) : ℝ) -
              realGeometricLogarithmicThreshold q C (Real.exp (-x))) / x)
        atTop
        (𝓝 (1 / (-Real.log q))) := by
    simpa only [add_zero] using hThresholdRatio.add hRoundDiv
  refine hSum.congr' ?_
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
  field_simp [hx]
  ring

/-- The exact strict stopping count has the precise logarithmic complexity
constant as the positive tolerance tends to zero. -/
theorem realGeometricExactStrictLogFloorIterationCount_div_log_oneDiv_tendsto
    (q C : ℝ)
    (hqPos : 0 < q)
    (hqLtOne : q < 1)
    (hC : 0 < C) :
    Tendsto
      (fun epsilon : ℝ =>
        (realGeometricExactStrictLogFloorIterationCount q C epsilon : ℝ) /
          Real.log (1 / epsilon))
      (𝓝[>] (0 : ℝ))
      (𝓝 (1 / (-Real.log q))) := by
  have hExpRatio :=
    realGeometricExactStrictLogFloorIterationCount_exp_neg_div_tendsto
      q C hqPos hqLtOne hC
  have hComp := hExpRatio.comp realLogOneDiv_tendsto_atTop_nhdsGT_zero
  refine hComp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with epsilon hEpsilon
  have hEpsilonPos : 0 < epsilon := hEpsilon
  have hInvPos : 0 < 1 / epsilon := one_div_pos.mpr hEpsilonPos
  simp only [Function.comp_apply]
  rw [Real.exp_neg, Real.exp_log hInvPos]
  simp [one_div]

local notation "q₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2

/-- Precise logarithmic complexity constant for the actual beta-zero
Green--Neumann operator-remainder count. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_div_log_oneDiv_tendsto :
    Tendsto
      (fun epsilon : ℝ =>
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount epsilon : ℝ) /
          Real.log (1 / epsilon))
      (𝓝[>] (0 : ℝ))
      (𝓝 (1 / (-Real.log ((323 : ℝ) / 325)))) := by
  simpa only [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount]
    using
      realGeometricExactStrictLogFloorIterationCount_div_log_oneDiv_tendsto
        q₀ 324
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.2
        (by norm_num)

/-- Precise logarithmic complexity constant for the actual beta-zero
Green--Neumann inverse-defect count. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_div_log_oneDiv_tendsto :
    Tendsto
      (fun epsilon : ℝ =>
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount epsilon : ℝ) /
          Real.log (1 / epsilon))
      (𝓝[>] (0 : ℝ))
      (𝓝 (1 / (-Real.log ((323 : ℝ) / 325)))) := by
  simpa only [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount]
    using
      realGeometricExactStrictLogFloorIterationCount_div_log_oneDiv_tendsto
        q₀ 1
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.2
        (by norm_num)

/-- Pointwise transfer of the operator-remainder logarithmic ratio from the
exact closed count to the canonical minimal stopping index. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex_div_log_oneDiv_eq_exact
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex
        epsilon hEpsilon : ℝ) / Real.log (1 / epsilon) =
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount
        epsilon : ℝ) / Real.log (1 / epsilon) := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex_eq_exactStrictLogFloorIterationCount
      epsilon hEpsilon]

/-- Pointwise transfer of the inverse-defect logarithmic ratio from the exact
closed count to the canonical minimal stopping index. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex_div_log_oneDiv_eq_exact
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex
        epsilon hEpsilon : ℝ) / Real.log (1 / epsilon) =
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount
        epsilon : ℝ) / Real.log (1 / epsilon) := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex_eq_exactStrictLogFloorIterationCount
      epsilon hEpsilon]

/-- Structured receipt for the exact logarithmic iteration-complexity constant
in the actual finite beta-zero optimal Richardson system. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonLogarithmicComplexityLimitL2Receipt :
    Prop where
  generic_limit :
    ∀ (q C : ℝ), 0 < q → q < 1 → 0 < C →
      Tendsto
        (fun epsilon : ℝ =>
          (realGeometricExactStrictLogFloorIterationCount q C epsilon : ℝ) /
            Real.log (1 / epsilon))
        (𝓝[>] (0 : ℝ))
        (𝓝 (1 / (-Real.log q)))
  operator_remainder_limit :
    Tendsto
      (fun epsilon : ℝ =>
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount epsilon : ℝ) /
          Real.log (1 / epsilon))
      (𝓝[>] (0 : ℝ))
      (𝓝 (1 / (-Real.log ((323 : ℝ) / 325))))
  inverse_defect_limit :
    Tendsto
      (fun epsilon : ℝ =>
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount epsilon : ℝ) /
          Real.log (1 / epsilon))
      (𝓝[>] (0 : ℝ))
      (𝓝 (1 / (-Real.log ((323 : ℝ) / 325))))
  claim_boundary : True

/-- The logarithmic complexity-limit receipt is inhabited. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonLogarithmicComplexityLimitL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonLogarithmicComplexityLimitL2Receipt := by
  exact
    { generic_limit :=
        realGeometricExactStrictLogFloorIterationCount_div_log_oneDiv_tendsto
      operator_remainder_limit :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_div_log_oneDiv_tendsto
      inverse_defect_limit :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_div_log_oneDiv_tendsto
      claim_boundary := trivial }

end
end MathlibAnalytic
end MGAP4D
