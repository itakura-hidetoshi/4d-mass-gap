import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanOptimalRichardsonJointScaleCovarianceL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter
open scoped BigOperators Function Topology

noncomputable section

set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 300000

/-- If a tolerance shrink factor lies between two consecutive powers of the
contraction factor, the exact strict stopping-count increment is one of the two
adjacent integers. This is the discrete core of logarithmic sensitivity. -/
theorem realGeometricExactStrictLogFloorIterationCount_mul_sensitivity_bracket
    (q C epsilon rho : ℝ)
    (hqPos : 0 < q)
    (hqLtOne : q < 1)
    (hC : 0 < C)
    (hEpsilon : 0 < epsilon)
    (hRhoPos : 0 < rho)
    (hCountPos :
      0 < realGeometricExactStrictLogFloorIterationCount q C epsilon)
    (m : ℕ)
    (hRhoLower : q ^ (m + 1) < rho)
    (hRhoUpper : rho ≤ q ^ m) :
    realGeometricExactStrictLogFloorIterationCount q C (rho * epsilon) =
        realGeometricExactStrictLogFloorIterationCount q C epsilon + m ∨
      realGeometricExactStrictLogFloorIterationCount q C (rho * epsilon) =
        realGeometricExactStrictLogFloorIterationCount q C epsilon + m + 1 := by
  let k := realGeometricExactStrictLogFloorIterationCount q C epsilon
  have hk : 0 < k := hCountPos
  have hScaledEpsilon : 0 < rho * epsilon := mul_pos hRhoPos hEpsilon
  have hInterval :
      C * q ^ k < epsilon ∧ epsilon ≤ C * q ^ (k - 1) :=
    (realGeometricExactStrictLogFloorIterationCount_eq_iff_error_interval
      q C epsilon hqPos hqLtOne hC hEpsilon k hk).1 rfl
  have hUpperCount :
      realGeometricExactStrictLogFloorIterationCount q C (rho * epsilon) ≤
        k + m + 1 := by
    apply
      (realGeometricExactStrictLogFloorIterationCount_le_iff
        q C (rho * epsilon) hqPos hqLtOne hC hScaledEpsilon
        (k + m + 1)).2
    have hProduct :
        (C * q ^ k) * q ^ (m + 1) < epsilon * rho :=
      mul_lt_mul hInterval.1 hRhoLower.le
        (pow_pos hqPos (m + 1))
        (mul_nonneg hC.le (pow_nonneg hqPos.le k))
    simpa [pow_add, mul_assoc, mul_left_comm, mul_comm] using hProduct
  have hLowerCount :
      k + m ≤
        realGeometricExactStrictLogFloorIterationCount q C (rho * epsilon) := by
    by_contra hNot
    have hCountLePrev :
        realGeometricExactStrictLogFloorIterationCount q C (rho * epsilon) ≤
          k + m - 1 := by
      omega
    have hPrevError :
        C * q ^ (k + m - 1) < rho * epsilon :=
      (realGeometricExactStrictLogFloorIterationCount_le_iff
        q C (rho * epsilon) hqPos hqLtOne hC hScaledEpsilon
        (k + m - 1)).1 hCountLePrev
    have hExponent : k + m - 1 = (k - 1) + m := by omega
    have hProduct :
        rho * epsilon ≤ q ^ m * (C * q ^ (k - 1)) :=
      mul_le_mul hRhoUpper hInterval.2 hEpsilon.le
        (pow_nonneg hqPos.le m)
    have hBoundary : rho * epsilon ≤ C * q ^ (k + m - 1) := by
      rw [hExponent, pow_add]
      simpa [mul_assoc, mul_left_comm, mul_comm] using hProduct
    exact (not_lt_of_ge hBoundary) hPrevError
  omega

/-- The same sensitivity bracket stated as an absolute increment bound. -/
theorem realGeometricExactStrictLogFloorIterationCount_mul_sensitivity_bounds
    (q C epsilon rho : ℝ)
    (hqPos : 0 < q)
    (hqLtOne : q < 1)
    (hC : 0 < C)
    (hEpsilon : 0 < epsilon)
    (hRhoPos : 0 < rho)
    (hCountPos :
      0 < realGeometricExactStrictLogFloorIterationCount q C epsilon)
    (m : ℕ)
    (hRhoLower : q ^ (m + 1) < rho)
    (hRhoUpper : rho ≤ q ^ m) :
    realGeometricExactStrictLogFloorIterationCount q C epsilon + m ≤
        realGeometricExactStrictLogFloorIterationCount q C (rho * epsilon) ∧
      realGeometricExactStrictLogFloorIterationCount q C (rho * epsilon) ≤
        realGeometricExactStrictLogFloorIterationCount q C epsilon + m + 1 := by
  rcases
      realGeometricExactStrictLogFloorIterationCount_mul_sensitivity_bracket
        q C epsilon rho hqPos hqLtOne hC hEpsilon hRhoPos hCountPos m
        hRhoLower hRhoUpper with h | h
  · omega
  · omega

local notation "q₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2
local notation "NJointExact" =>
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount

/-- Actual beta-zero simultaneous stopping-count sensitivity under an arbitrary
positive shrink factor bracketed by consecutive powers of `q₀ = 323 / 325`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_mul_sensitivity_bracket
    (epsilon rho : ℝ)
    (hEpsilon : 0 < epsilon)
    (hEpsilonLe : epsilon ≤ (324 : ℝ))
    (hRhoPos : 0 < rho)
    (m : ℕ)
    (hRhoLower : q₀ ^ (m + 1) < rho)
    (hRhoUpper : rho ≤ q₀ ^ m) :
    NJointExact (rho * epsilon) = NJointExact epsilon + m ∨
      NJointExact (rho * epsilon) = NJointExact epsilon + m + 1 := by
  have hScaledEpsilon : 0 < rho * epsilon := mul_pos hRhoPos hEpsilon
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_eq_remainderExactStrictLogFloorIterationCount
      (rho * epsilon) hScaledEpsilon,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_eq_remainderExactStrictLogFloorIterationCount
      epsilon hEpsilon]
  change
    realGeometricExactStrictLogFloorIterationCount q₀ 324 (rho * epsilon) =
          realGeometricExactStrictLogFloorIterationCount q₀ 324 epsilon + m ∨
      realGeometricExactStrictLogFloorIterationCount q₀ 324 (rho * epsilon) =
          realGeometricExactStrictLogFloorIterationCount q₀ 324 epsilon + m + 1
  have hCountPosJoint : 0 < NJointExact epsilon :=
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_pos_iff
      epsilon hEpsilon).2 hEpsilonLe
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_eq_remainderExactStrictLogFloorIterationCount
      epsilon hEpsilon] at hCountPosJoint
  change 0 < realGeometricExactStrictLogFloorIterationCount q₀ 324 epsilon at hCountPosJoint
  exact
    realGeometricExactStrictLogFloorIterationCount_mul_sensitivity_bracket
      q₀ 324 epsilon rho
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.2
      (by norm_num) hEpsilon hRhoPos hCountPosJoint m hRhoLower hRhoUpper

/-- Actual beta-zero simultaneous logarithmic-sensitivity bounds. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_mul_sensitivity_bounds
    (epsilon rho : ℝ)
    (hEpsilon : 0 < epsilon)
    (hEpsilonLe : epsilon ≤ (324 : ℝ))
    (hRhoPos : 0 < rho)
    (m : ℕ)
    (hRhoLower : q₀ ^ (m + 1) < rho)
    (hRhoUpper : rho ≤ q₀ ^ m) :
    NJointExact epsilon + m ≤ NJointExact (rho * epsilon) ∧
      NJointExact (rho * epsilon) ≤ NJointExact epsilon + m + 1 := by
  rcases
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_mul_sensitivity_bracket
        epsilon rho hEpsilon hEpsilonLe hRhoPos m hRhoLower hRhoUpper with h | h
  · omega
  · omega

/-- Structured receipt for the generic and actual logarithmic-sensitivity core. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonJointLogarithmicSensitivityL2Receipt :
    Prop where
  generic_bracket :
    ∀ (q C epsilon rho : ℝ), 0 < q → q < 1 → 0 < C → 0 < epsilon →
      0 < rho → 0 < realGeometricExactStrictLogFloorIterationCount q C epsilon →
      ∀ (m : ℕ), q ^ (m + 1) < rho → rho ≤ q ^ m →
        realGeometricExactStrictLogFloorIterationCount q C (rho * epsilon) =
            realGeometricExactStrictLogFloorIterationCount q C epsilon + m ∨
          realGeometricExactStrictLogFloorIterationCount q C (rho * epsilon) =
            realGeometricExactStrictLogFloorIterationCount q C epsilon + m + 1
  actual_bracket :
    ∀ (epsilon rho : ℝ), 0 < epsilon → epsilon ≤ (324 : ℝ) → 0 < rho →
      ∀ (m : ℕ), q₀ ^ (m + 1) < rho → rho ≤ q₀ ^ m →
        NJointExact (rho * epsilon) = NJointExact epsilon + m ∨
          NJointExact (rho * epsilon) = NJointExact epsilon + m + 1
  actual_bounds :
    ∀ (epsilon rho : ℝ), 0 < epsilon → epsilon ≤ (324 : ℝ) → 0 < rho →
      ∀ (m : ℕ), q₀ ^ (m + 1) < rho → rho ≤ q₀ ^ m →
        NJointExact epsilon + m ≤ NJointExact (rho * epsilon) ∧
          NJointExact (rho * epsilon) ≤ NJointExact epsilon + m + 1
  claim_boundary : True

/-- The joint logarithmic-sensitivity receipt is inhabited. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonJointLogarithmicSensitivityL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonJointLogarithmicSensitivityL2Receipt := by
  exact
    { generic_bracket :=
        realGeometricExactStrictLogFloorIterationCount_mul_sensitivity_bracket
      actual_bracket :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_mul_sensitivity_bracket
      actual_bounds :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_mul_sensitivity_bounds
      claim_boundary := trivial }

end
end MathlibAnalytic
end MGAP4D
