import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanOptimalRichardsonJointSharpThresholdL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter
open scoped BigOperators Function Topology

noncomputable section

set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 300000

/-- In the nontrivial regime, scaling a positive strict geometric tolerance by
`q ^ m` increases the exact stopping count by exactly `m`. -/
theorem realGeometricExactStrictLogFloorIterationCount_pow_mul_scale_covariant
    (q C epsilon : ℝ)
    (hqPos : 0 < q)
    (hqLtOne : q < 1)
    (hC : 0 < C)
    (hEpsilon : 0 < epsilon)
    (hCountPos :
      0 < realGeometricExactStrictLogFloorIterationCount q C epsilon)
    (m : ℕ) :
    realGeometricExactStrictLogFloorIterationCount q C (q ^ m * epsilon) =
      realGeometricExactStrictLogFloorIterationCount q C epsilon + m := by
  let k := realGeometricExactStrictLogFloorIterationCount q C epsilon
  have hk : 0 < k := hCountPos
  have hScaledEpsilon : 0 < q ^ m * epsilon :=
    mul_pos (pow_pos hqPos m) hEpsilon
  have hInterval :
      C * q ^ k < epsilon ∧ epsilon ≤ C * q ^ (k - 1) :=
    (realGeometricExactStrictLogFloorIterationCount_eq_iff_error_interval
      q C epsilon hqPos hqLtOne hC hEpsilon k hk).1 rfl
  apply
    (realGeometricExactStrictLogFloorIterationCount_eq_iff_error_interval
      q C (q ^ m * epsilon) hqPos hqLtOne hC hScaledEpsilon
      (k + m) (by omega)).2
  constructor
  · rw [pow_add]
    have hPowPos : 0 < q ^ m := pow_pos hqPos m
    nlinarith
  · have hExponent : k + m - 1 = (k - 1) + m := by omega
    rw [hExponent, pow_add]
    have hPowNonneg : 0 ≤ q ^ m := (pow_pos hqPos m).le
    exact mul_le_mul_of_nonneg_left hInterval.2 hPowNonneg

/-- One-step form of exact geometric scale covariance. -/
theorem realGeometricExactStrictLogFloorIterationCount_mul_scale_covariant
    (q C epsilon : ℝ)
    (hqPos : 0 < q)
    (hqLtOne : q < 1)
    (hC : 0 < C)
    (hEpsilon : 0 < epsilon)
    (hCountPos :
      0 < realGeometricExactStrictLogFloorIterationCount q C epsilon) :
    realGeometricExactStrictLogFloorIterationCount q C (q * epsilon) =
      realGeometricExactStrictLogFloorIterationCount q C epsilon + 1 := by
  simpa using
    realGeometricExactStrictLogFloorIterationCount_pow_mul_scale_covariant
      q C epsilon hqPos hqLtOne hC hEpsilon hCountPos 1

local notation "q₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2
local notation "NJointExact" =>
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount

/-- Actual beta-zero simultaneous exact stopping count under arbitrary
contraction-power rescaling of a nontrivial tolerance. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_pow_mul_scale_covariant
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon)
    (hEpsilonLe : epsilon ≤ (324 : ℝ))
    (m : ℕ) :
    NJointExact (q₀ ^ m * epsilon) = NJointExact epsilon + m := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_eq_remainderExactStrictLogFloorIterationCount
      (q₀ ^ m * epsilon)
      (mul_pos (pow_pos
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1
        m) hEpsilon),
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_eq_remainderExactStrictLogFloorIterationCount
      epsilon hEpsilon]
  change
    realGeometricExactStrictLogFloorIterationCount q₀ 324 (q₀ ^ m * epsilon) =
      realGeometricExactStrictLogFloorIterationCount q₀ 324 epsilon + m
  exact
    realGeometricExactStrictLogFloorIterationCount_pow_mul_scale_covariant
      q₀ 324 epsilon
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.2
      (by norm_num) hEpsilon
      ((periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_pos_iff
        epsilon hEpsilon).2 hEpsilonLe)
      m

/-- Actual one-step beta-zero simultaneous scale covariance. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_mul_scale_covariant
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon)
    (hEpsilonLe : epsilon ≤ (324 : ℝ)) :
    NJointExact (q₀ * epsilon) = NJointExact epsilon + 1 := by
  simpa using
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_pow_mul_scale_covariant
      epsilon hEpsilon hEpsilonLe 1

/-- Iterated scaling starting at the maximal nontrivial tolerance `324` gives an
exact count equal to the scaling exponent. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_at_scaled_prefactor
    (m : ℕ) :
    NJointExact (q₀ ^ m * 324) = m + 1 := by
  have hBase : NJointExact (324 : ℝ) = 1 := by
    exact
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_eq_iff_error_interval
        324 (by norm_num) 1 (by norm_num)).2 (by
          constructor
          · change (324 : ℝ) * q₀ < 324
            have hqLt :=
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.2
            nlinarith
          · norm_num)
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_pow_mul_scale_covariant
      324 (by norm_num) le_rfl m,
    hBase]
  omega

/-- Structured receipt for the generic and actual scale-covariant iteration laws. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonJointScaleCovarianceL2Receipt :
    Prop where
  generic_pow_scale :
    ∀ (q C epsilon : ℝ), 0 < q → q < 1 → 0 < C → 0 < epsilon →
      0 < realGeometricExactStrictLogFloorIterationCount q C epsilon →
      ∀ (m : ℕ),
        realGeometricExactStrictLogFloorIterationCount q C (q ^ m * epsilon) =
          realGeometricExactStrictLogFloorIterationCount q C epsilon + m
  actual_pow_scale :
    ∀ (epsilon : ℝ), 0 < epsilon → epsilon ≤ (324 : ℝ) → ∀ (m : ℕ),
      NJointExact (q₀ ^ m * epsilon) = NJointExact epsilon + m
  actual_one_step :
    ∀ (epsilon : ℝ), 0 < epsilon → epsilon ≤ (324 : ℝ) →
      NJointExact (q₀ * epsilon) = NJointExact epsilon + 1
  scaled_prefactor :
    ∀ (m : ℕ), NJointExact (q₀ ^ m * 324) = m + 1
  claim_boundary : True

/-- The joint scale-covariance receipt is inhabited. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonJointScaleCovarianceL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonJointScaleCovarianceL2Receipt := by
  exact
    { generic_pow_scale :=
        realGeometricExactStrictLogFloorIterationCount_pow_mul_scale_covariant
      actual_pow_scale :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_pow_mul_scale_covariant
      actual_one_step :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_mul_scale_covariant
      scaled_prefactor :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_at_scaled_prefactor
      claim_boundary := trivial }

end
end MathlibAnalytic
end MGAP4D
