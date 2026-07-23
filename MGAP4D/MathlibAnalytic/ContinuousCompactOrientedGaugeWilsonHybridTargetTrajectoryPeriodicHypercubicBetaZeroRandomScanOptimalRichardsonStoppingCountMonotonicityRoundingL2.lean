import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanOptimalRichardsonExactStrictLogFloorIterationCountsL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000

/-- Enlarging the tolerance cannot increase the exact strict geometric stopping
count. -/
theorem realGeometricExactStrictLogFloorIterationCount_antitone_epsilon
    (q C epsilon₁ epsilon₂ : ℝ)
    (hqPos : 0 < q)
    (hqLtOne : q < 1)
    (hC : 0 < C)
    (hEpsilon₁ : 0 < epsilon₁)
    (hEpsilon₂ : 0 < epsilon₂)
    (hEpsilon : epsilon₁ ≤ epsilon₂) :
    realGeometricExactStrictLogFloorIterationCount q C epsilon₂ ≤
      realGeometricExactStrictLogFloorIterationCount q C epsilon₁ := by
  apply
    (realGeometricExactStrictLogFloorIterationCount_isLeast
      q C epsilon₂ hqPos hqLtOne hC hEpsilon₂).2
  intro n hn
  exact lt_of_lt_of_le
    ((realGeometricExactStrictLogFloorIterationCount_le_iff
      q C epsilon₁ hqPos hqLtOne hC hEpsilon₁ n).1 hn)
    hEpsilon

/-- The exact strict count is zero precisely when the tolerance already exceeds
the initial geometric prefactor. -/
theorem realGeometricExactStrictLogFloorIterationCount_eq_zero_iff
    (q C epsilon : ℝ)
    (hqPos : 0 < q)
    (hqLtOne : q < 1)
    (hC : 0 < C)
    (hEpsilon : 0 < epsilon) :
    realGeometricExactStrictLogFloorIterationCount q C epsilon = 0 ↔
      C < epsilon := by
  constructor
  · intro hCount
    have hLe :
        realGeometricExactStrictLogFloorIterationCount q C epsilon ≤ 0 := by
      omega
    simpa using
      (realGeometricExactStrictLogFloorIterationCount_le_iff
        q C epsilon hqPos hqLtOne hC hEpsilon 0).1 hLe
  · intro hInitial
    have hLe :
        realGeometricExactStrictLogFloorIterationCount q C epsilon ≤ 0 :=
      (realGeometricExactStrictLogFloorIterationCount_le_iff
        q C epsilon hqPos hqLtOne hC hEpsilon 0).2
        (by simpa using hInitial)
    omega

/-- Staircase characterization: the exact strict count is `n + 1` exactly when
the tolerance lies strictly above the next geometric level and at or below the
preceding level. -/
theorem realGeometricExactStrictLogFloorIterationCount_eq_succ_iff
    (q C epsilon : ℝ)
    (hqPos : 0 < q)
    (hqLtOne : q < 1)
    (hC : 0 < C)
    (hEpsilon : 0 < epsilon)
    (n : ℕ) :
    realGeometricExactStrictLogFloorIterationCount q C epsilon = n + 1 ↔
      C * q ^ (n + 1) < epsilon ∧ epsilon ≤ C * q ^ n := by
  constructor
  · intro hCount
    have hNextLe :
        realGeometricExactStrictLogFloorIterationCount q C epsilon ≤ n + 1 := by
      omega
    have hNext :=
      (realGeometricExactStrictLogFloorIterationCount_le_iff
        q C epsilon hqPos hqLtOne hC hEpsilon (n + 1)).1 hNextLe
    have hNotLe :
        ¬ realGeometricExactStrictLogFloorIterationCount q C epsilon ≤ n := by
      omega
    have hNotPrev : ¬ C * q ^ n < epsilon := by
      intro hPrev
      exact hNotLe
        ((realGeometricExactStrictLogFloorIterationCount_le_iff
          q C epsilon hqPos hqLtOne hC hEpsilon n).2 hPrev)
    exact ⟨hNext, le_of_not_gt hNotPrev⟩
  · rintro ⟨hNext, hPrev⟩
    have hNextLe :
        realGeometricExactStrictLogFloorIterationCount q C epsilon ≤ n + 1 :=
      (realGeometricExactStrictLogFloorIterationCount_le_iff
        q C epsilon hqPos hqLtOne hC hEpsilon (n + 1)).2 hNext
    have hNotLe :
        ¬ realGeometricExactStrictLogFloorIterationCount q C epsilon ≤ n := by
      intro hLe
      have hStrict :=
        (realGeometricExactStrictLogFloorIterationCount_le_iff
          q C epsilon hqPos hqLtOne hC hEpsilon n).1 hLe
      exact (not_lt_of_ge hPrev) hStrict
    omega

/-- When the tolerance is at most the initial prefactor, the logarithmic
threshold is nonnegative. -/
theorem realGeometricLogarithmicThreshold_nonneg
    (q C epsilon : ℝ)
    (hqPos : 0 < q)
    (hqLtOne : q < 1)
    (hC : 0 < C)
    (hEpsilon : 0 < epsilon)
    (hEpsilonLeC : epsilon ≤ C) :
    0 ≤ realGeometricLogarithmicThreshold q C epsilon := by
  apply le_of_not_gt
  intro hThreshold
  have hInitial : C < epsilon := by
    have h :=
      (realGeometricLogarithmicThreshold_lt_nat_iff
        q C epsilon hqPos hqLtOne hC hEpsilon 0).1
        (by simpa using hThreshold)
    simpa using h
  exact (not_lt_of_ge hEpsilonLeC) hInitial

/-- The logarithmic threshold is strictly below the exact strict natural count.
This holds even when the count is zero. -/
theorem realGeometricLogarithmicThreshold_lt_exactStrictLogFloorIterationCount
    (q C epsilon : ℝ)
    (hqPos : 0 < q)
    (hqLtOne : q < 1)
    (hC : 0 < C)
    (hEpsilon : 0 < epsilon) :
    realGeometricLogarithmicThreshold q C epsilon <
      (realGeometricExactStrictLogFloorIterationCount q C epsilon : ℝ) := by
  exact
    (realGeometricLogarithmicThreshold_lt_nat_iff
      q C epsilon hqPos hqLtOne hC hEpsilon
      (realGeometricExactStrictLogFloorIterationCount q C epsilon)).2
      (realGeometricExactStrictLogFloorIterationCount_spec
        q C epsilon hqPos hqLtOne hC hEpsilon)

/-- In the nontrivial regime `epsilon ≤ C`, the exact strict count is at most
one above its real logarithmic threshold. -/
theorem realGeometricExactStrictLogFloorIterationCount_le_threshold_add_one
    (q C epsilon : ℝ)
    (hqPos : 0 < q)
    (hqLtOne : q < 1)
    (hC : 0 < C)
    (hEpsilon : 0 < epsilon)
    (hEpsilonLeC : epsilon ≤ C) :
    (realGeometricExactStrictLogFloorIterationCount q C epsilon : ℝ) ≤
      realGeometricLogarithmicThreshold q C epsilon + 1 := by
  have hNotInitial : ¬ C < epsilon := not_lt.mpr hEpsilonLeC
  have hThresholdNonneg :=
    realGeometricLogarithmicThreshold_nonneg
      q C epsilon hqPos hqLtOne hC hEpsilon hEpsilonLeC
  simp only [realGeometricExactStrictLogFloorIterationCount, hNotInitial, if_false,
    Nat.cast_add, Nat.cast_one]
  calc
    (⌊realGeometricLogarithmicThreshold q C epsilon⌋₊ : ℝ) + 1 =
        1 + (⌊realGeometricLogarithmicThreshold q C epsilon⌋₊ : ℝ) := add_comm _ _
    _ ≤ 1 + realGeometricLogarithmicThreshold q C epsilon :=
      add_le_add_left (Nat.floor_le hThresholdNonneg) 1
    _ = realGeometricLogarithmicThreshold q C epsilon + 1 := add_comm _ _

/-- The integer-rounding error of the exact strict count lies in `(0, 1]`. This
is the explicit bounded `O(1)` remainder around the logarithmic threshold. -/
theorem realGeometricExactStrictLogFloorIterationCount_sub_threshold_mem_Ioc
    (q C epsilon : ℝ)
    (hqPos : 0 < q)
    (hqLtOne : q < 1)
    (hC : 0 < C)
    (hEpsilon : 0 < epsilon)
    (hEpsilonLeC : epsilon ≤ C) :
    (realGeometricExactStrictLogFloorIterationCount q C epsilon : ℝ) -
        realGeometricLogarithmicThreshold q C epsilon ∈ Set.Ioc 0 1 := by
  constructor
  · linarith only [realGeometricLogarithmicThreshold_lt_exactStrictLogFloorIterationCount
      q C epsilon hqPos hqLtOne hC hEpsilon]
  · linarith only [realGeometricExactStrictLogFloorIterationCount_le_threshold_add_one
      q C epsilon hqPos hqLtOne hC hEpsilon hEpsilonLeC]

/-- Absolute form of the explicit `O(1)` rounding estimate. -/
theorem realGeometricExactStrictLogFloorIterationCount_abs_sub_threshold_le_one
    (q C epsilon : ℝ)
    (hqPos : 0 < q)
    (hqLtOne : q < 1)
    (hC : 0 < C)
    (hEpsilon : 0 < epsilon)
    (hEpsilonLeC : epsilon ≤ C) :
    |(realGeometricExactStrictLogFloorIterationCount q C epsilon : ℝ) -
        realGeometricLogarithmicThreshold q C epsilon| ≤ 1 := by
  have hRound :=
    realGeometricExactStrictLogFloorIterationCount_sub_threshold_mem_Ioc
      q C epsilon hqPos hqLtOne hC hEpsilon hEpsilonLeC
  rw [abs_of_nonneg hRound.1.le]
  exact hRound.2

local notation "q₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2
local notation "Rem₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannRemainderEndL2
local notation "Def₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannInverseDefectEndL2

/-- The exact strict operator-remainder count is antitone in the tolerance. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_antitone
    (epsilon₁ epsilon₂ : ℝ)
    (hEpsilon₁ : 0 < epsilon₁)
    (hEpsilon₂ : 0 < epsilon₂)
    (hEpsilon : epsilon₁ ≤ epsilon₂) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount epsilon₂ ≤
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount epsilon₁ :=
  realGeometricExactStrictLogFloorIterationCount_antitone_epsilon
    q₀ 324 epsilon₁ epsilon₂
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.2
    (by norm_num) hEpsilon₁ hEpsilon₂ hEpsilon

/-- The canonical minimal strict operator-remainder count is antitone in the
tolerance. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex_antitone
    (epsilon₁ epsilon₂ : ℝ)
    (hEpsilon₁ : 0 < epsilon₁)
    (hEpsilon₂ : 0 < epsilon₂)
    (hEpsilon : epsilon₁ ≤ epsilon₂) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex
        epsilon₂ hEpsilon₂ ≤
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex
        epsilon₁ hEpsilon₁ := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex_eq_exactStrictLogFloorIterationCount
      epsilon₂ hEpsilon₂,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex_eq_exactStrictLogFloorIterationCount
      epsilon₁ hEpsilon₁]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_antitone
      epsilon₁ epsilon₂ hEpsilon₁ hEpsilon₂ hEpsilon

/-- The exact operator-remainder count vanishes precisely above its initial norm
`324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_eq_zero_iff
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount epsilon = 0 ↔
      (324 : ℝ) < epsilon :=
  realGeometricExactStrictLogFloorIterationCount_eq_zero_iff
    q₀ 324 epsilon
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.2
    (by norm_num) hEpsilon

/-- Staircase characterization of the exact strict operator-remainder count. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_eq_succ_iff
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon)
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount epsilon = n + 1 ↔
      ‖Rem₀ (n + 1)‖ < epsilon ∧ epsilon ≤ ‖Rem₀ n‖ := by
  simpa only [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonGreenNeumannRemainderEndL2_eq] using
    realGeometricExactStrictLogFloorIterationCount_eq_succ_iff
      q₀ 324 epsilon
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.2
      (by norm_num) hEpsilon n

/-- The exact operator-remainder count differs from its closed logarithmic
threshold by a number in `(0, 1]`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_sub_logarithmicThreshold_mem_Ioc
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon)
    (hEpsilonLe : epsilon ≤ 324) :
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount epsilon : ℝ) -
        realGeometricLogarithmicThreshold q₀ 324 epsilon ∈ Set.Ioc 0 1 :=
  realGeometricExactStrictLogFloorIterationCount_sub_threshold_mem_Ioc
    q₀ 324 epsilon
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.2
    (by norm_num) hEpsilon hEpsilonLe

/-- The exact strict inverse-defect count is antitone in the tolerance. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_antitone
    (epsilon₁ epsilon₂ : ℝ)
    (hEpsilon₁ : 0 < epsilon₁)
    (hEpsilon₂ : 0 < epsilon₂)
    (hEpsilon : epsilon₁ ≤ epsilon₂) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount epsilon₂ ≤
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount epsilon₁ :=
  realGeometricExactStrictLogFloorIterationCount_antitone_epsilon
    q₀ 1 epsilon₁ epsilon₂
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.2
    (by norm_num) hEpsilon₁ hEpsilon₂ hEpsilon

/-- The canonical minimal strict inverse-defect count is antitone in the
tolerance. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex_antitone
    (epsilon₁ epsilon₂ : ℝ)
    (hEpsilon₁ : 0 < epsilon₁)
    (hEpsilon₂ : 0 < epsilon₂)
    (hEpsilon : epsilon₁ ≤ epsilon₂) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex
        epsilon₂ hEpsilon₂ ≤
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex
        epsilon₁ hEpsilon₁ := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex_eq_exactStrictLogFloorIterationCount
      epsilon₂ hEpsilon₂,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex_eq_exactStrictLogFloorIterationCount
      epsilon₁ hEpsilon₁]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_antitone
      epsilon₁ epsilon₂ hEpsilon₁ hEpsilon₂ hEpsilon

/-- The exact inverse-defect count vanishes precisely above its initial norm
`1`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_eq_zero_iff
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount epsilon = 0 ↔
      (1 : ℝ) < epsilon :=
  realGeometricExactStrictLogFloorIterationCount_eq_zero_iff
    q₀ 1 epsilon
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.2
    (by norm_num) hEpsilon

/-- Staircase characterization of the exact strict inverse-defect count. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_eq_succ_iff
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon)
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount epsilon = n + 1 ↔
      ‖Def₀ (n + 1)‖ < epsilon ∧ epsilon ≤ ‖Def₀ n‖ := by
  simpa only [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonGreenNeumannInverseDefectEndL2_eq,
    one_mul] using
    realGeometricExactStrictLogFloorIterationCount_eq_succ_iff
      q₀ 1 epsilon
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.2
      (by norm_num) hEpsilon n

/-- The exact inverse-defect count differs from its closed logarithmic threshold
by a number in `(0, 1]`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_sub_logarithmicThreshold_mem_Ioc
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon)
    (hEpsilonLe : epsilon ≤ 1) :
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount epsilon : ℝ) -
        realGeometricLogarithmicThreshold q₀ 1 epsilon ∈ Set.Ioc 0 1 :=
  realGeometricExactStrictLogFloorIterationCount_sub_threshold_mem_Ioc
    q₀ 1 epsilon
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.2
    (by norm_num) hEpsilon hEpsilonLe

/-- Structured receipt for tolerance monotonicity, staircase structure, and
explicit logarithmic rounding control. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStoppingCountMonotonicityRoundingL2Receipt :
    Prop where
  generic_antitone :
    ∀ (q C epsilon₁ epsilon₂ : ℝ), 0 < q → q < 1 → 0 < C →
      0 < epsilon₁ → 0 < epsilon₂ → epsilon₁ ≤ epsilon₂ →
      realGeometricExactStrictLogFloorIterationCount q C epsilon₂ ≤
        realGeometricExactStrictLogFloorIterationCount q C epsilon₁
  generic_staircase :
    ∀ (q C epsilon : ℝ), 0 < q → q < 1 → 0 < C → 0 < epsilon →
      ∀ n : ℕ,
        realGeometricExactStrictLogFloorIterationCount q C epsilon = n + 1 ↔
          C * q ^ (n + 1) < epsilon ∧ epsilon ≤ C * q ^ n
  generic_rounding :
    ∀ (q C epsilon : ℝ), 0 < q → q < 1 → 0 < C → 0 < epsilon → epsilon ≤ C →
      (realGeometricExactStrictLogFloorIterationCount q C epsilon : ℝ) -
          realGeometricLogarithmicThreshold q C epsilon ∈ Set.Ioc 0 1
  operator_remainder_antitone :
    ∀ (epsilon₁ epsilon₂ : ℝ), 0 < epsilon₁ → 0 < epsilon₂ → epsilon₁ ≤ epsilon₂ →
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount epsilon₂ ≤
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount epsilon₁
  inverse_defect_antitone :
    ∀ (epsilon₁ epsilon₂ : ℝ), 0 < epsilon₁ → 0 < epsilon₂ → epsilon₁ ≤ epsilon₂ →
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount epsilon₂ ≤
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount epsilon₁
  claim_boundary : True

/-- The stopping-count monotonicity and rounding receipt is inhabited. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStoppingCountMonotonicityRoundingL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStoppingCountMonotonicityRoundingL2Receipt := by
  exact
    { generic_antitone :=
        realGeometricExactStrictLogFloorIterationCount_antitone_epsilon
      generic_staircase :=
        realGeometricExactStrictLogFloorIterationCount_eq_succ_iff
      generic_rounding :=
        realGeometricExactStrictLogFloorIterationCount_sub_threshold_mem_Ioc
      operator_remainder_antitone :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_antitone
      inverse_defect_antitone :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_antitone
      claim_boundary := trivial }

end
end MathlibAnalytic
end MGAP4D
