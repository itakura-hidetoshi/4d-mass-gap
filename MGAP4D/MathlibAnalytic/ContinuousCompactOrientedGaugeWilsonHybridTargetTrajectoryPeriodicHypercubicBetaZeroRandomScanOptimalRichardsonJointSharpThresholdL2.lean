import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanOptimalRichardsonJointExactStoppingDecisionL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter
open scoped BigOperators Function Topology

noncomputable section

set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 300000

/-- A positive exact strict geometric stopping count equals `k` exactly on the
half-open tolerance interval between the errors at indices `k` and `k - 1`. -/
theorem realGeometricExactStrictLogFloorIterationCount_eq_iff_error_interval
    (q C epsilon : ℝ)
    (hqPos : 0 < q)
    (hqLtOne : q < 1)
    (hC : 0 < C)
    (hEpsilon : 0 < epsilon)
    (k : ℕ)
    (hk : 0 < k) :
    realGeometricExactStrictLogFloorIterationCount q C epsilon = k ↔
      C * q ^ k < epsilon ∧ epsilon ≤ C * q ^ (k - 1) := by
  constructor
  · intro hCount
    constructor
    · rw [← hCount]
      exact
        realGeometricExactStrictLogFloorIterationCount_spec
          q C epsilon hqPos hqLtOne hC hEpsilon
    · by_contra hPrev
      have hPrevLt : C * q ^ (k - 1) < epsilon := lt_of_not_ge hPrev
      have hCountLePrev :
          realGeometricExactStrictLogFloorIterationCount q C epsilon ≤ k - 1 :=
        (realGeometricExactStrictLogFloorIterationCount_le_iff
          q C epsilon hqPos hqLtOne hC hEpsilon (k - 1)).2 hPrevLt
      rw [hCount] at hCountLePrev
      omega
  · intro hInterval
    have hCountLe :
        realGeometricExactStrictLogFloorIterationCount q C epsilon ≤ k :=
      (realGeometricExactStrictLogFloorIterationCount_le_iff
        q C epsilon hqPos hqLtOne hC hEpsilon k).2 hInterval.1
    have hNotCountLePrev :
        ¬ realGeometricExactStrictLogFloorIterationCount q C epsilon ≤ k - 1 := by
      intro hCountLePrev
      have hPrevLt : C * q ^ (k - 1) < epsilon :=
        (realGeometricExactStrictLogFloorIterationCount_le_iff
          q C epsilon hqPos hqLtOne hC hEpsilon (k - 1)).1 hCountLePrev
      exact (not_lt_of_ge hInterval.2) hPrevLt
    omega

local notation "q₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2
local notation "Rem₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannRemainderEndL2
local notation "Def₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannInverseDefectEndL2
local notation "NJointExact" =>
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount

/-- Every positive iteration count `k` is attained by the actual simultaneous
beta-zero stopping problem exactly on its sharp half-open tolerance interval. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_eq_iff_error_interval
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon)
    (k : ℕ)
    (hk : 0 < k) :
    NJointExact epsilon = k ↔
      (324 : ℝ) * ((323 : ℝ) / 325) ^ k < epsilon ∧
        epsilon ≤ (324 : ℝ) * ((323 : ℝ) / 325) ^ (k - 1) := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_eq_remainderExactStrictLogFloorIterationCount
      epsilon hEpsilon]
  change
    realGeometricExactStrictLogFloorIterationCount q₀ 324 epsilon = k ↔
      (324 : ℝ) * q₀ ^ k < epsilon ∧
        epsilon ≤ (324 : ℝ) * q₀ ^ (k - 1)
  exact
    realGeometricExactStrictLogFloorIterationCount_eq_iff_error_interval
      q₀ 324 epsilon
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.2
      (by norm_num) hEpsilon k hk

/-- At the proof-independent exact simultaneous stopping count both targets hold. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_spec
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ‖Rem₀ (NJointExact epsilon)‖ < epsilon ∧
      ‖Def₀ (NJointExact epsilon)‖ < epsilon :=
  (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_le_iff
    epsilon hEpsilon (NJointExact epsilon)).1 le_rfl

/-- Whenever the exact simultaneous stopping count is positive, the preceding
index does not yet satisfy both targets. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_predecessor_not_spec
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon)
    (hCountPos : 0 < NJointExact epsilon) :
    ¬ (‖Rem₀ (NJointExact epsilon - 1)‖ < epsilon ∧
        ‖Def₀ (NJointExact epsilon - 1)‖ < epsilon) := by
  intro hPrev
  have hCountLePrev : NJointExact epsilon ≤ NJointExact epsilon - 1 :=
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_le_iff
      epsilon hEpsilon (NJointExact epsilon - 1)).2 hPrev
  omega

/-- Sharp threshold certificate: the exact count succeeds, while its predecessor
fails whenever that predecessor exists. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_sharpThreshold
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon)
    (hCountPos : 0 < NJointExact epsilon) :
    (‖Rem₀ (NJointExact epsilon)‖ < epsilon ∧
        ‖Def₀ (NJointExact epsilon)‖ < epsilon) ∧
      ¬ (‖Rem₀ (NJointExact epsilon - 1)‖ < epsilon ∧
          ‖Def₀ (NJointExact epsilon - 1)‖ < epsilon) := by
  exact
    ⟨periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_spec
        epsilon hEpsilon,
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_predecessor_not_spec
        epsilon hEpsilon hCountPos⟩

/-- The positive-count condition is equivalent to the nontrivial tolerance
regime `epsilon ≤ 324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_pos_iff
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    0 < NJointExact epsilon ↔ epsilon ≤ (324 : ℝ) := by
  rw [Nat.pos_iff_ne_zero]
  constructor
  · intro hNe
    apply le_of_not_gt
    intro hLt
    exact hNe
      ((periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_eq_zero_iff
        epsilon hEpsilon).2 hLt)
  · intro hLe hZero
    exact (not_lt_of_ge hLe)
      ((periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_eq_zero_iff
        epsilon hEpsilon).1 hZero)

/-- In the entire nontrivial tolerance regime, the exact simultaneous count is a
sharp transition between failure at the predecessor and success at the count. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_nontrivialTolerance_sharpThreshold
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon)
    (hEpsilonLe : epsilon ≤ (324 : ℝ)) :
    (‖Rem₀ (NJointExact epsilon)‖ < epsilon ∧
        ‖Def₀ (NJointExact epsilon)‖ < epsilon) ∧
      ¬ (‖Rem₀ (NJointExact epsilon - 1)‖ < epsilon ∧
          ‖Def₀ (NJointExact epsilon - 1)‖ < epsilon) := by
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_sharpThreshold
      epsilon hEpsilon
      ((periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_pos_iff
        epsilon hEpsilon).2 hEpsilonLe)

/-- Structured receipt for sharp tolerance intervals and predecessor failure in
the actual finite beta-zero simultaneous Richardson stopping problem. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonJointSharpThresholdL2Receipt :
    Prop where
  generic_interval :
    ∀ (q C epsilon : ℝ), 0 < q → q < 1 → 0 < C → 0 < epsilon →
      ∀ (k : ℕ), 0 < k →
        (realGeometricExactStrictLogFloorIterationCount q C epsilon = k ↔
          C * q ^ k < epsilon ∧ epsilon ≤ C * q ^ (k - 1))
  actual_interval :
    ∀ (epsilon : ℝ), 0 < epsilon → ∀ (k : ℕ), 0 < k →
      (NJointExact epsilon = k ↔
        (324 : ℝ) * ((323 : ℝ) / 325) ^ k < epsilon ∧
          epsilon ≤ (324 : ℝ) * ((323 : ℝ) / 325) ^ (k - 1))
  exact_spec :
    ∀ (epsilon : ℝ), 0 < epsilon →
      ‖Rem₀ (NJointExact epsilon)‖ < epsilon ∧
        ‖Def₀ (NJointExact epsilon)‖ < epsilon
  predecessor_failure :
    ∀ (epsilon : ℝ), 0 < epsilon → 0 < NJointExact epsilon →
      ¬ (‖Rem₀ (NJointExact epsilon - 1)‖ < epsilon ∧
          ‖Def₀ (NJointExact epsilon - 1)‖ < epsilon)
  nontrivial_sharp_threshold :
    ∀ (epsilon : ℝ), 0 < epsilon → epsilon ≤ (324 : ℝ) →
      (‖Rem₀ (NJointExact epsilon)‖ < epsilon ∧
          ‖Def₀ (NJointExact epsilon)‖ < epsilon) ∧
        ¬ (‖Rem₀ (NJointExact epsilon - 1)‖ < epsilon ∧
            ‖Def₀ (NJointExact epsilon - 1)‖ < epsilon)
  claim_boundary : True

/-- The joint sharp-threshold receipt is inhabited. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonJointSharpThresholdL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonJointSharpThresholdL2Receipt := by
  exact
    { generic_interval :=
        realGeometricExactStrictLogFloorIterationCount_eq_iff_error_interval
      actual_interval :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_eq_iff_error_interval
      exact_spec :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_spec
      predecessor_failure :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_predecessor_not_spec
      nontrivial_sharp_threshold :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_nontrivialTolerance_sharpThreshold
      claim_boundary := trivial }

end
end MathlibAnalytic
end MGAP4D
