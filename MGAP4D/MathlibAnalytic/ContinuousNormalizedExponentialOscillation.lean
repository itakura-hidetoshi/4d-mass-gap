import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Partition function of a continuous exponential weight over a compact
probability space. -/
def continuousExpPartition
    {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X)
    (logWeight : X → ℝ) : ℝ :=
  ∫ x, Real.exp (logWeight x) ∂μ

/-- Normalized continuous exponential density. -/
def continuousNormalizedExp
    {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X)
    (logWeight : X → ℝ)
    (x : X) : ℝ :=
  Real.exp (logWeight x) / continuousExpPartition μ logWeight

/-- A continuous exponential partition function over a compact probability
space is strictly positive. -/
theorem continuousExpPartition_pos
    {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X)
    [IsProbabilityMeasure μ]
    (logWeight : X → ℝ)
    (hContinuous : Continuous logWeight) :
    0 < continuousExpPartition μ logWeight := by
  unfold continuousExpPartition
  exact integral_exp_pos
    ((Real.continuous_exp.comp hContinuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))

/-- Oscillation control of a continuous log-weight difference gives the sharp
mutual likelihood-ratio bound after integral normalization. -/
theorem continuousNormalizedExp_mutual_le_exp_mul_of_difference_oscillation
    {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X)
    [IsProbabilityMeasure μ]
    (logWeight referenceLogWeight : X → ℝ)
    (hLog : Continuous logWeight)
    (hRef : Continuous referenceLogWeight)
    (R : ℝ)
    (hOsc : ∀ x y : X,
      (logWeight x - referenceLogWeight x) -
          (logWeight y - referenceLogWeight y) ≤ R)
    (x : X) :
    continuousNormalizedExp μ logWeight x ≤
        Real.exp R * continuousNormalizedExp μ referenceLogWeight x ∧
      continuousNormalizedExp μ referenceLogWeight x ≤
        Real.exp R * continuousNormalizedExp μ logWeight x := by
  have hZ : 0 < continuousExpPartition μ logWeight :=
    continuousExpPartition_pos μ logWeight hLog
  have hZref : 0 < continuousExpPartition μ referenceLogWeight :=
    continuousExpPartition_pos μ referenceLogWeight hRef
  constructor
  · unfold continuousNormalizedExp
    rw [show Real.exp R *
        (Real.exp (referenceLogWeight x) /
          continuousExpPartition μ referenceLogWeight) =
      (Real.exp R * Real.exp (referenceLogWeight x)) /
        continuousExpPartition μ referenceLogWeight by ring]
    apply (div_le_div_iff₀ hZ hZref).2
    unfold continuousExpPartition
    rw [← integral_const_mul, ← integral_const_mul]
    exact integral_mono (Filter.Eventually.of_forall fun y => by
      calc
        Real.exp (logWeight x) * Real.exp (referenceLogWeight y) =
            Real.exp (logWeight x + referenceLogWeight y) := by
              rw [← Real.exp_add]
        _ ≤ Real.exp (R + referenceLogWeight x + logWeight y) := by
          apply Real.exp_le_exp.mpr
          linarith [hOsc x y]
        _ = Real.exp R * Real.exp (referenceLogWeight x) *
            Real.exp (logWeight y) := by
          rw [Real.exp_add, Real.exp_add])
  · unfold continuousNormalizedExp
    rw [show Real.exp R *
        (Real.exp (logWeight x) / continuousExpPartition μ logWeight) =
      (Real.exp R * Real.exp (logWeight x)) /
        continuousExpPartition μ logWeight by ring]
    apply (div_le_div_iff₀ hZref hZ).2
    unfold continuousExpPartition
    rw [← integral_const_mul, ← integral_const_mul]
    exact integral_mono (Filter.Eventually.of_forall fun y => by
      calc
        Real.exp (referenceLogWeight x) * Real.exp (logWeight y) =
            Real.exp (referenceLogWeight x + logWeight y) := by
              rw [← Real.exp_add]
        _ ≤ Real.exp (R + logWeight x + referenceLogWeight y) := by
          apply Real.exp_le_exp.mpr
          linarith [hOsc y x]
        _ = Real.exp R * Real.exp (logWeight x) *
            Real.exp (referenceLogWeight y) := by
          rw [Real.exp_add, Real.exp_add])

end
end MathlibAnalytic
end MGAP4D
