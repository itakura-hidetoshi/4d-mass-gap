import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanOptimalRichardsonJointGlobalExecutionBudgetL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter
open scoped BigOperators Function Topology

noncomputable section

set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 300000

local notation "Rem₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannRemainderEndL2
local notation "Def₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannInverseDefectEndL2
local notation "NRemExact" =>
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount
local notation "NDefExact" =>
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount
local notation "NJoint" =>
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_minimalStoppingIndex

/-- Proof-independent exact strict stopping count for the simultaneous actual
beta-zero operator-remainder and inverse-defect targets. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount
    (epsilon : ℝ) : ℕ :=
  max (NRemExact epsilon) (NDefExact epsilon)

local notation "NJointExact" =>
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount

/-- At every positive tolerance, the proof-independent joint exact count is the
operator-remainder exact count because the latter dominates the inverse-defect
count. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_eq_remainderExactStrictLogFloorIterationCount
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    NJointExact epsilon = NRemExact epsilon := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount
  exact max_eq_left
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_le_remainderExactStrictLogFloorIterationCount
      epsilon hEpsilon)

/-- Closed floor/log formula for the proof-independent simultaneous exact count
at every positive tolerance. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_eq
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    NJointExact epsilon =
      if (324 : ℝ) < epsilon then 0 else
        ⌊Real.log ((324 : ℝ) / epsilon) /
          (-Real.log ((323 : ℝ) / 325))⌋₊ + 1 := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_eq_remainderExactStrictLogFloorIterationCount
      epsilon hEpsilon]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_eq
      epsilon

/-- The proof-independent joint exact count is zero exactly when the tolerance
already strictly exceeds the larger initial prefactor `324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_eq_zero_iff
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    NJointExact epsilon = 0 ↔ (324 : ℝ) < epsilon := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_eq_remainderExactStrictLogFloorIterationCount
      epsilon hEpsilon]
  change
    realGeometricExactStrictLogFloorIterationCount
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2
        324 epsilon = 0 ↔
      (324 : ℝ) < epsilon
  exact
    realGeometricExactStrictLogFloorIterationCount_eq_zero_iff
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2
      324 epsilon
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.2
      (by norm_num)
      hEpsilon

/-- The canonical proof-selected simultaneous minimal index is exactly the
proof-independent joint exact count. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_minimalStoppingIndex_eq_exactStrictLogFloorIterationCount
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    NJoint epsilon hEpsilon = NJointExact epsilon := by
  calc
    NJoint epsilon hEpsilon =
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex
          epsilon hEpsilon :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_minimalStoppingIndex_eq_remainderMinimalStoppingIndex
        epsilon hEpsilon
    _ = NRemExact epsilon :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex_eq_exactStrictLogFloorIterationCount
        epsilon hEpsilon
    _ = NJointExact epsilon :=
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_eq_remainderExactStrictLogFloorIterationCount
        epsilon hEpsilon).symm

/-- Closed floor/log formula for every proof-selected canonical simultaneous
minimal stopping index. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_minimalStoppingIndex_eq
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    NJoint epsilon hEpsilon =
      if (324 : ℝ) < epsilon then 0 else
        ⌊Real.log ((324 : ℝ) / epsilon) /
          (-Real.log ((323 : ℝ) / 325))⌋₊ + 1 := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_minimalStoppingIndex_eq_exactStrictLogFloorIterationCount
      epsilon hEpsilon]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_eq
      epsilon hEpsilon

/-- Exact pointwise simultaneous stopping decision: an index is at or after the
proof-independent joint exact count exactly when both actual norms are strictly
below the requested positive tolerance. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_le_iff
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon)
    (n : ℕ) :
    NJointExact epsilon ≤ n ↔
      ‖Rem₀ n‖ < epsilon ∧ ‖Def₀ n‖ < epsilon := by
  constructor
  · intro h
    have hRemExact : NRemExact epsilon ≤ n := by
      rw [
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_eq_remainderExactStrictLogFloorIterationCount
          epsilon hEpsilon] at h
      exact h
    constructor
    · exact
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_le_iff
          epsilon hEpsilon n).1 hRemExact
    · exact
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_le_iff
          epsilon hEpsilon n).1
          ((periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_le_remainderExactStrictLogFloorIterationCount
            epsilon hEpsilon).trans hRemExact)
  · intro h
    rw [
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_eq_remainderExactStrictLogFloorIterationCount
        epsilon hEpsilon]
    exact
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_le_iff
        epsilon hEpsilon n).2 h.1

/-- Equivalent pointwise simultaneous stopping decision for every proof-selected
canonical joint minimal index. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_minimalStoppingIndex_le_iff
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon)
    (n : ℕ) :
    NJoint epsilon hEpsilon ≤ n ↔
      ‖Rem₀ n‖ < epsilon ∧ ‖Def₀ n‖ < epsilon := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_minimalStoppingIndex_eq_exactStrictLogFloorIterationCount
      epsilon hEpsilon]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_le_iff
      epsilon hEpsilon n

/-- Fully expanded closed-form stopping decision, with no proof-selected index on
the left-hand side. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_closedFormula_le_iff
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon)
    (n : ℕ) :
    (if (324 : ℝ) < epsilon then 0 else
        ⌊Real.log ((324 : ℝ) / epsilon) /
          (-Real.log ((323 : ℝ) / 325))⌋₊ + 1) ≤ n ↔
      ‖Rem₀ n‖ < epsilon ∧ ‖Def₀ n‖ < epsilon := by
  rw [←
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_eq
      epsilon hEpsilon]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_le_iff
      epsilon hEpsilon n

/-- The proof-independent joint exact count is also an exact decision boundary
for the full permanent simultaneous-tail predicate. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_le_iff_permanentTail
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon)
    (N : ℕ) :
    NJointExact epsilon ≤ N ↔
      ∀ n ≥ N, ‖Rem₀ n‖ < epsilon ∧ ‖Def₀ n‖ < epsilon := by
  constructor
  · intro h n hn
    exact
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_le_iff
        epsilon hEpsilon n).1
        (h.trans hn)
  · intro h
    exact
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_le_iff
        epsilon hEpsilon N).2
        (h N le_rfl)

/-- The proof-independent exact count is the least permanent simultaneous
stopping index. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_isLeast
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    IsLeast
      {N : ℕ | ∀ n ≥ N, ‖Rem₀ n‖ < epsilon ∧ ‖Def₀ n‖ < epsilon}
      (NJointExact epsilon) := by
  constructor
  · intro n hn
    exact
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_le_iff
        epsilon hEpsilon n).1 hn
  · intro N hN
    exact
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_le_iff
        epsilon hEpsilon N).2
        (hN N le_rfl)

/-- Structured receipt for the proof-independent exact simultaneous stopping
count, its closed formula, and its complete pointwise and permanent-tail
decision characterizations. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonJointExactStoppingDecisionL2Receipt :
    Prop where
  exact_eq_remainder_exact :
    ∀ (epsilon : ℝ), 0 < epsilon →
      NJointExact epsilon = NRemExact epsilon
  exact_closed_formula :
    ∀ (epsilon : ℝ), 0 < epsilon →
      NJointExact epsilon =
        if (324 : ℝ) < epsilon then 0 else
          ⌊Real.log ((324 : ℝ) / epsilon) /
            (-Real.log ((323 : ℝ) / 325))⌋₊ + 1
  canonical_eq_exact :
    ∀ (epsilon : ℝ) (hEpsilon : 0 < epsilon),
      NJoint epsilon hEpsilon = NJointExact epsilon
  pointwise_decision :
    ∀ (epsilon : ℝ) (hEpsilon : 0 < epsilon) (n : ℕ),
      NJointExact epsilon ≤ n ↔
        ‖Rem₀ n‖ < epsilon ∧ ‖Def₀ n‖ < epsilon
  permanent_tail_decision :
    ∀ (epsilon : ℝ) (hEpsilon : 0 < epsilon) (N : ℕ),
      NJointExact epsilon ≤ N ↔
        ∀ n ≥ N, ‖Rem₀ n‖ < epsilon ∧ ‖Def₀ n‖ < epsilon
  exact_isLeast :
    ∀ (epsilon : ℝ) (hEpsilon : 0 < epsilon),
      IsLeast
        {N : ℕ | ∀ n ≥ N, ‖Rem₀ n‖ < epsilon ∧ ‖Def₀ n‖ < epsilon}
        (NJointExact epsilon)
  claim_boundary : True

/-- The joint exact stopping-decision receipt is inhabited. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonJointExactStoppingDecisionL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonJointExactStoppingDecisionL2Receipt := by
  exact
    { exact_eq_remainder_exact :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_eq_remainderExactStrictLogFloorIterationCount
      exact_closed_formula :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_eq
      canonical_eq_exact :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_minimalStoppingIndex_eq_exactStrictLogFloorIterationCount
      pointwise_decision :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_le_iff
      permanent_tail_decision :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_le_iff_permanentTail
      exact_isLeast :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannJointEndL2_exactStrictLogFloorIterationCount_isLeast
      claim_boundary := trivial }

end
end MathlibAnalytic
end MGAP4D
