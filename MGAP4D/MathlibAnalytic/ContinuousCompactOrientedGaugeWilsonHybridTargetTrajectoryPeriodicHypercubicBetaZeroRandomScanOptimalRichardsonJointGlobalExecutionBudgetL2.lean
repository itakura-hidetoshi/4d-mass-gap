import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanOptimalRichardsonGlobalExecutionBudgetL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter
open scoped BigOperators Function Topology

noncomputable section

set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 300000

/-- Increasing the positive geometric prefactor cannot decrease the exact strict
stopping count. -/
theorem realGeometricExactStrictLogFloorIterationCount_mono_prefactor
    (q C₁ C₂ epsilon : ℝ)
    (hqPos : 0 < q)
    (hqLtOne : q < 1)
    (hC₁ : 0 < C₁)
    (hC₂ : 0 < C₂)
    (hEpsilon : 0 < epsilon)
    (hC : C₁ ≤ C₂) :
    realGeometricExactStrictLogFloorIterationCount q C₁ epsilon ≤
      realGeometricExactStrictLogFloorIterationCount q C₂ epsilon := by
  apply
    (realGeometricExactStrictLogFloorIterationCount_le_iff
      q C₁ epsilon hqPos hqLtOne hC₁ hEpsilon
      (realGeometricExactStrictLogFloorIterationCount q C₂ epsilon)).2
  have hLarge :=
    realGeometricExactStrictLogFloorIterationCount_spec
      q C₂ epsilon hqPos hqLtOne hC₂ hEpsilon
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right hC
      (pow_nonneg hqPos.le
        (realGeometricExactStrictLogFloorIterationCount q C₂ epsilon)))
    hLarge

/-- A permanent geometric tail for a larger prefactor transfers to every
smaller prefactor. -/
theorem realGeometricStrictPermanentTail_mono_prefactor
    (q C₁ C₂ epsilon : ℝ)
    (hqNonneg : 0 ≤ q)
    (hC : C₁ ≤ C₂)
    (N : ℕ)
    (hTail : ∀ n ≥ N, C₂ * q ^ n < epsilon) :
    ∀ n ≥ N, C₁ * q ^ n < epsilon := by
  intro n hn
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right hC (pow_nonneg hqNonneg n))
    (hTail n hn)

/-- A global budget built for a larger prefactor also bounds the exact strict
count for every smaller positive prefactor. -/
theorem realGeometricExactStrictLogFloorIterationCount_le_globalStrictExecutionBudget_of_prefactor_le
    (q K C₁ C₂ epsilon : ℝ)
    (hqPos : 0 < q)
    (hqLtOne : q < 1)
    (hC₁ : 0 < C₁)
    (hC₂ : 0 < C₂)
    (hEpsilon : 0 < epsilon)
    (hC : C₁ ≤ C₂)
    (hK : 1 / (-Real.log q) < K) :
    realGeometricExactStrictLogFloorIterationCount q C₁ epsilon ≤
      realGeometricGlobalStrictExecutionBudget K C₂ epsilon :=
  (realGeometricExactStrictLogFloorIterationCount_mono_prefactor
    q C₁ C₂ epsilon hqPos hqLtOne hC₁ hC₂ hEpsilon hC).trans
    (realGeometricExactStrictLogFloorIterationCount_le_globalStrictExecutionBudget
      q K C₂ epsilon hqPos hqLtOne hC₂ hEpsilon hK)

/-- A global budget built for a larger prefactor gives a permanent strict tail
for every smaller positive prefactor. -/
theorem realGeometricGlobalStrictExecutionBudget_permanentTail_of_prefactor_le
    (q K C₁ C₂ epsilon : ℝ)
    (hqPos : 0 < q)
    (hqLtOne : q < 1)
    (hC₁ : 0 < C₁)
    (hC₂ : 0 < C₂)
    (hEpsilon : 0 < epsilon)
    (hC : C₁ ≤ C₂)
    (hK : 1 / (-Real.log q) < K) :
    ∀ n ≥ realGeometricGlobalStrictExecutionBudget K C₂ epsilon,
      C₁ * q ^ n < epsilon :=
  realGeometricStrictPermanentTail_mono_prefactor
    q C₁ C₂ epsilon hqPos.le hC
    (realGeometricGlobalStrictExecutionBudget K C₂ epsilon)
    (realGeometricGlobalStrictExecutionBudget_permanentTail
      q K C₂ epsilon hqPos hqLtOne hC₂ hEpsilon hK)

local notation "q₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2
local notation "Rem₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannRemainderEndL2
local notation "Def₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannInverseDefectEndL2
local notation "NRem" =>
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex
local notation "NDef" =>
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex
local notation "BRem" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannRemainderEndL2GlobalExecutionBudget

/-- A single global execution budget for simultaneously controlling the actual
beta-zero operator remainder and inverse defect.  It is the larger-prefactor
operator-remainder budget. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonJointGlobalExecutionBudgetL2
    (epsilon : ℝ) : ℕ :=
  BRem epsilon

/-- The canonical simultaneous minimal stopping index is the maximum of the two
canonical componentwise minimal stopping indices. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_minimalStoppingIndex
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) : ℕ :=
  max (NRem epsilon hEpsilon) (NDef epsilon hEpsilon)

local notation "BJoint" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonJointGlobalExecutionBudgetL2
local notation "NJoint" =>
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_minimalStoppingIndex

/-- Closed piecewise formula for the single joint global execution budget. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonJointGlobalExecutionBudgetL2_eq
    (epsilon : ℝ) :
    BJoint epsilon =
      if (324 : ℝ) < epsilon then 0 else
        ⌈(162 : ℝ) * Real.log ((324 : ℝ) / epsilon) + 1⌉₊ := by
  rfl

private theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonJoint_logarithmicComplexityCoefficient_lt_162 :
    1 / (-Real.log q₀) < (162 : ℝ) := by
  change 1 / (-Real.log ((323 : ℝ) / 325)) < (162 : ℝ)
  exact
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardson_logarithmicComplexityConstant_lt_162

/-- The exact inverse-defect count is never larger than the exact
operator-remainder count at the same positive tolerance. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_le_remainderExactStrictLogFloorIterationCount
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount epsilon ≤
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount epsilon := by
  change realGeometricExactStrictLogFloorIterationCount q₀ 1 epsilon ≤
    realGeometricExactStrictLogFloorIterationCount q₀ 324 epsilon
  exact
    realGeometricExactStrictLogFloorIterationCount_mono_prefactor
      q₀ 1 324 epsilon
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.2
      (by norm_num) (by norm_num) hEpsilon (by norm_num)

/-- The canonical inverse-defect minimal index is never larger than the
canonical operator-remainder minimal index. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex_le_remainderMinimalStoppingIndex
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    NDef epsilon hEpsilon ≤ NRem epsilon hEpsilon := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex_eq_exactStrictLogFloorIterationCount
      epsilon hEpsilon,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex_eq_exactStrictLogFloorIterationCount
      epsilon hEpsilon]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_le_remainderExactStrictLogFloorIterationCount
      epsilon hEpsilon

/-- The canonical simultaneous minimal index is exactly the operator-remainder
minimal index because the latter dominates the inverse-defect minimal index. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_minimalStoppingIndex_eq_remainderMinimalStoppingIndex
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    NJoint epsilon hEpsilon = NRem epsilon hEpsilon := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_minimalStoppingIndex
  exact max_eq_left
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex_le_remainderMinimalStoppingIndex
      epsilon hEpsilon)

/-- The single joint budget globally bounds both exact componentwise stopping
counts for every positive tolerance. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactCounts_le_jointGlobalExecutionBudget
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount epsilon ≤
        BJoint epsilon ∧
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount epsilon ≤
        BJoint epsilon := by
  constructor
  · exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_le_globalExecutionBudget
        epsilon hEpsilon
  · change realGeometricExactStrictLogFloorIterationCount q₀ 1 epsilon ≤
      realGeometricGlobalStrictExecutionBudget 162 324 epsilon
    exact
      realGeometricExactStrictLogFloorIterationCount_le_globalStrictExecutionBudget_of_prefactor_le
        q₀ 162 1 324 epsilon
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.2
        (by norm_num) (by norm_num) hEpsilon (by norm_num)
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonJoint_logarithmicComplexityCoefficient_lt_162

/-- The single joint budget globally bounds both proof-selected canonical
componentwise minimal stopping indices. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_componentMinimalIndices_le_jointGlobalExecutionBudget
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    NRem epsilon hEpsilon ≤ BJoint epsilon ∧
      NDef epsilon hEpsilon ≤ BJoint epsilon := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex_eq_exactStrictLogFloorIterationCount
      epsilon hEpsilon,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex_eq_exactStrictLogFloorIterationCount
      epsilon hEpsilon]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactCounts_le_jointGlobalExecutionBudget
      epsilon hEpsilon

/-- Every index at or above the single joint budget simultaneously and
permanently meets both actual beta-zero error targets. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_jointGlobalExecutionBudget_permanentTail
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∀ n ≥ BJoint epsilon,
      ‖Rem₀ n‖ < epsilon ∧ ‖Def₀ n‖ < epsilon := by
  intro n hn
  have hExact :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactCounts_le_jointGlobalExecutionBudget
      epsilon hEpsilon
  constructor
  · exact
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_le_iff
        epsilon hEpsilon n).1
        (hExact.1.trans hn)
  · exact
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_le_iff
        epsilon hEpsilon n).1
        (hExact.2.trans hn)

/-- In particular, the single joint budget simultaneously meets both actual
beta-zero error targets. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_jointGlobalExecutionBudget_spec
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ‖Rem₀ (BJoint epsilon)‖ < epsilon ∧
      ‖Def₀ (BJoint epsilon)‖ < epsilon :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_jointGlobalExecutionBudget_permanentTail
    epsilon hEpsilon (BJoint epsilon) le_rfl

/-- The maximum of the two canonical componentwise minimal indices is the least
permanent index satisfying both actual beta-zero error targets simultaneously. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_minimalStoppingIndex_isLeast
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    IsLeast
      {N : ℕ | ∀ n ≥ N, ‖Rem₀ n‖ < epsilon ∧ ‖Def₀ n‖ < epsilon}
      (NJoint epsilon hEpsilon) := by
  have hRem :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex_isLeast
      epsilon hEpsilon
  have hDef :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex_isLeast
      epsilon hEpsilon
  unfold periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_minimalStoppingIndex
  constructor
  · intro n hn
    constructor
    · exact hRem.1 n ((le_max_left _ _).trans hn)
    · exact hDef.1 n ((le_max_right _ _).trans hn)
  · intro N hN
    apply max_le
    · exact hRem.2 (by
        intro n hn
        exact (hN n hn).1)
    · exact hDef.2 (by
        intro n hn
        exact (hN n hn).2)

/-- The canonical simultaneous minimal stopping index is globally bounded by
the single joint execution budget. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_minimalStoppingIndex_le_jointGlobalExecutionBudget
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    NJoint epsilon hEpsilon ≤ BJoint epsilon :=
  (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_minimalStoppingIndex_isLeast
    epsilon hEpsilon).2
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_jointGlobalExecutionBudget_permanentTail
      epsilon hEpsilon)

/-- Structured receipt for the single global execution budget and the canonical
simultaneous minimal stopping index in the actual finite beta-zero Richardson
system. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonJointGlobalExecutionBudgetL2Receipt :
    Prop where
  generic_exact_prefactor_mono :
    ∀ (q C₁ C₂ epsilon : ℝ), 0 < q → q < 1 → 0 < C₁ → 0 < C₂ →
      0 < epsilon → C₁ ≤ C₂ →
      realGeometricExactStrictLogFloorIterationCount q C₁ epsilon ≤
        realGeometricExactStrictLogFloorIterationCount q C₂ epsilon
  generic_tail_prefactor_mono :
    ∀ (q C₁ C₂ epsilon : ℝ), 0 ≤ q → C₁ ≤ C₂ → ∀ N : ℕ,
      (∀ n ≥ N, C₂ * q ^ n < epsilon) →
      ∀ n ≥ N, C₁ * q ^ n < epsilon
  inverse_minimal_le_remainder_minimal :
    ∀ (epsilon : ℝ) (hEpsilon : 0 < epsilon),
      NDef epsilon hEpsilon ≤ NRem epsilon hEpsilon
  joint_minimal_eq_remainder_minimal :
    ∀ (epsilon : ℝ) (hEpsilon : 0 < epsilon),
      NJoint epsilon hEpsilon = NRem epsilon hEpsilon
  joint_minimal_isLeast :
    ∀ (epsilon : ℝ) (hEpsilon : 0 < epsilon),
      IsLeast
        {N : ℕ | ∀ n ≥ N, ‖Rem₀ n‖ < epsilon ∧ ‖Def₀ n‖ < epsilon}
        (NJoint epsilon hEpsilon)
  joint_budget_exact_upper :
    ∀ (epsilon : ℝ), 0 < epsilon →
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount epsilon ≤
          BJoint epsilon ∧
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount epsilon ≤
          BJoint epsilon
  joint_budget_permanent_tail :
    ∀ (epsilon : ℝ), 0 < epsilon →
      ∀ n ≥ BJoint epsilon,
        ‖Rem₀ n‖ < epsilon ∧ ‖Def₀ n‖ < epsilon
  joint_minimal_le_budget :
    ∀ (epsilon : ℝ) (hEpsilon : 0 < epsilon),
      NJoint epsilon hEpsilon ≤ BJoint epsilon
  claim_boundary : True

/-- The joint global execution-budget receipt is inhabited. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonJointGlobalExecutionBudgetL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonJointGlobalExecutionBudgetL2Receipt := by
  exact
    { generic_exact_prefactor_mono :=
        realGeometricExactStrictLogFloorIterationCount_mono_prefactor
      generic_tail_prefactor_mono :=
        realGeometricStrictPermanentTail_mono_prefactor
      inverse_minimal_le_remainder_minimal :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex_le_remainderMinimalStoppingIndex
      joint_minimal_eq_remainder_minimal :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_minimalStoppingIndex_eq_remainderMinimalStoppingIndex
      joint_minimal_isLeast :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_minimalStoppingIndex_isLeast
      joint_budget_exact_upper :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactCounts_le_jointGlobalExecutionBudget
      joint_budget_permanent_tail :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_jointGlobalExecutionBudget_permanentTail
      joint_minimal_le_budget :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_minimalStoppingIndex_le_jointGlobalExecutionBudget
      claim_boundary := trivial }

end
end MathlibAnalytic
end MGAP4D
