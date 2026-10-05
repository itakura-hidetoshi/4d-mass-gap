import MGAP4D.MathlibAnalytic.ContinuousNormalizedExponentialOscillation
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonSingleLinkSharpTV
import Mathlib.Tactic

/-!
# Continuous cross-ratio control implies sharp normalized total variation

The ground-state one-link law is a normalized positive fiber weight.  For
locality estimates, the normalization denominator should not be bounded
separately: a four-point cross-ratio, equivalently an oscillation bound for the
difference of two complete log weights, survives normalization with only one
exponential factor.

This file packages that generic compact-probability-space statement.  If two
continuous complete log weights have difference oscillation at most `R`, then
their normalized exponential densities have half-L1 distance at most

  (exp R - 1) / (exp R + 1).

This is exactly the total-variation normalization needed before inserting the
continuous physical-vacuum mixed-link estimate.  No lattice, gauge, transfer,
Euclidean-time, or mass-gap claim is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Multiplicative four-point cross-ratio control written in the additive
complete-log-weight form that is stable under normalization. -/
def ContinuousNormalizedExpCrossRatioBound
    {X : Type*}
    (logWeight referenceLogWeight : X → ℝ)
    (R : ℝ) : Prop :=
  ∀ x y : X,
    (logWeight x - referenceLogWeight x) -
        (logWeight y - referenceLogWeight y) ≤ R

/-- A normalized continuous exponential density is continuous. -/
theorem continuous_continuousNormalizedExp
    {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X)
    (logWeight : X → ℝ)
    (hLog : Continuous logWeight) :
    Continuous (continuousNormalizedExp μ logWeight) := by
  unfold continuousNormalizedExp
  exact (Real.continuous_exp.comp hLog).div_const _

/-- A normalized continuous exponential density is nonnegative. -/
theorem continuousNormalizedExp_nonneg
    {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X)
    [IsProbabilityMeasure μ]
    (logWeight : X → ℝ)
    (hLog : Continuous logWeight)
    (x : X) :
    0 ≤ continuousNormalizedExp μ logWeight x := by
  unfold continuousNormalizedExp
  exact div_nonneg
    (Real.exp_nonneg _)
    (le_of_lt (continuousExpPartition_pos μ logWeight hLog))

/-- A normalized continuous exponential density integrates to one. -/
theorem integral_continuousNormalizedExp_eq_one
    {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X)
    [IsProbabilityMeasure μ]
    (logWeight : X → ℝ)
    (hLog : Continuous logWeight) :
    ∫ x, continuousNormalizedExp μ logWeight x ∂μ = 1 := by
  have hZ : continuousExpPartition μ logWeight ≠ 0 :=
    ne_of_gt (continuousExpPartition_pos μ logWeight hLog)
  unfold continuousNormalizedExp
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const]
  unfold continuousExpPartition
  exact mul_inv_cancel₀ hZ

/-- Complete-log-weight cross-ratio control yields mutual pointwise
likelihood-ratio domination of the normalized densities. -/
theorem continuousNormalizedExp_mutual_le_exp_mul_of_crossRatio
    {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X)
    [IsProbabilityMeasure μ]
    (logWeight referenceLogWeight : X → ℝ)
    (hLog : Continuous logWeight)
    (hRef : Continuous referenceLogWeight)
    (R : ℝ)
    (hCross :
      ContinuousNormalizedExpCrossRatioBound
        logWeight referenceLogWeight R)
    (x : X) :
    continuousNormalizedExp μ logWeight x ≤
        Real.exp R * continuousNormalizedExp μ referenceLogWeight x ∧
      continuousNormalizedExp μ referenceLogWeight x ≤
        Real.exp R * continuousNormalizedExp μ logWeight x := by
  exact
    continuousNormalizedExp_mutual_le_exp_mul_of_difference_oscillation
      μ logWeight referenceLogWeight hLog hRef R hCross x

/-- Sharp total-variation consequence of a complete-log-weight cross-ratio
radius.  The quantity on the left is the standard half-L1 distance of the two
normalized densities. -/
theorem continuousNormalizedExp_halfL1_le_of_crossRatio
    {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X)
    [IsProbabilityMeasure μ]
    (logWeight referenceLogWeight : X → ℝ)
    (hLog : Continuous logWeight)
    (hRef : Continuous referenceLogWeight)
    (R : ℝ)
    (hR : 0 ≤ R)
    (hCross :
      ContinuousNormalizedExpCrossRatioBound
        logWeight referenceLogWeight R) :
    (2 : ℝ)⁻¹ *
        ∫ x,
          |continuousNormalizedExp μ logWeight x -
            continuousNormalizedExp μ referenceLogWeight x| ∂μ ≤
      (Real.exp R - 1) / (Real.exp R + 1) := by
  apply
    continuous_probabilityDensity_halfL1_le_of_mutual_le_mul
      μ
      (continuousNormalizedExp μ logWeight)
      (continuousNormalizedExp μ referenceLogWeight)
      (continuous_continuousNormalizedExp μ logWeight hLog)
      (continuous_continuousNormalizedExp μ referenceLogWeight hRef)
      (integral_continuousNormalizedExp_eq_one μ logWeight hLog)
      (integral_continuousNormalizedExp_eq_one μ referenceLogWeight hRef)
      (Real.exp R)
      (Real.one_le_exp hR)
      (continuousNormalizedExp_nonneg μ logWeight hLog)
      (continuousNormalizedExp_nonneg μ referenceLogWeight hRef)
  · intro x
    exact
      (continuousNormalizedExp_mutual_le_exp_mul_of_crossRatio
        μ logWeight referenceLogWeight hLog hRef R hCross x).1
  · intro x
    exact
      (continuousNormalizedExp_mutual_le_exp_mul_of_crossRatio
        μ logWeight referenceLogWeight hLog hRef R hCross x).2

end

end MathlibAnalytic
end MGAP4D
