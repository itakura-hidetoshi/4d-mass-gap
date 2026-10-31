import MGAP4D.MathlibAnalytic.CompactSymmetricMomentRegions

/-!
# P4-Q2-PZ37ACN — quantitative upper tails from an actual positive mean

For a continuous real function on the original compact probability space,
its proved finite upper cap R and actual mean M > 0 force a strict upper
tail beyond M/2. The exact, denominator-sensitive estimate is
  M / (2 R - M) <= measure.real {x | M/2 < f x}.
No atom-free, concentration, independence, or uniform-volume hypothesis
is used. This applies to the squared original Wilson four-mode amplitude.
-/

namespace MGAP4D.MathlibAnalytic.CompactPositiveMomentTail

open MeasureTheory
open scoped Topology
noncomputable section
set_option autoImplicit false

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
  [CompactSpace α] [BorelSpace α]
  (μ : Measure α) [IsProbabilityMeasure μ]

/-- A strict positive-mean upper tail has an explicit positive mass floor
determined only by the actual mean and a proved pointwise cap. -/
theorem half_mean_upper_tail
    (f : α → ℝ) (hf : Continuous f) (R : ℝ)
    (hBound : ∀ x, f x ≤ R) (hM : 0 < ∫ x, f x ∂μ) :
    0 < 2 * R - (∫ x, f x ∂μ) ∧
      (∫ x, f x ∂μ) / (2 * R - (∫ x, f x ∂μ)) ≤
        Measure.real μ {x | (∫ y, f y ∂μ) / 2 < f x} := by
  classical
  let M : ℝ := ∫ x, f x ∂μ
  let P : Set α := {x | M / 2 < f x}
  have hI : Integrable f μ :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hMR : M ≤ R := by
    change (∫ x, f x ∂μ) ≤ R
    calc
      (∫ x, f x ∂μ) ≤ ∫ _x : α, R ∂μ :=
        integral_mono hI (integrable_const _) hBound
      _ = R := by simp
  have hDen : 0 < 2 * R - M := by
    have hM' : 0 < M := hM
    linarith
  have hP : MeasurableSet P :=
    (isOpen_lt continuous_const hf).measurableSet
  have hPI : Integrable (P.indicator (fun _ : α => (1 : ℝ))) μ :=
    (integrable_const _).indicator hP
  have hConstI : Integrable (fun _x : α => M / 2) μ := integrable_const _
  have hMulI : Integrable (fun x : α =>
      (R - M / 2) * P.indicator (fun _ => (1 : ℝ)) x) μ :=
    hPI.const_mul _
  have hUpperI : Integrable (fun x : α =>
      M / 2 + (R - M / 2) * P.indicator (fun _ => (1 : ℝ)) x) μ :=
    hConstI.add hMulI
  have hPoint (x : α) :
      f x ≤ M / 2 + (R - M / 2) * P.indicator (fun _ => (1 : ℝ)) x := by
    by_cases hp : x ∈ P
    · rw [Set.indicator_of_mem hp]
      nlinarith [hBound x]
    · rw [Set.indicator_of_notMem hp]
      have hx : f x ≤ M / 2 := le_of_not_gt hp
      simpa using hx
  have hIntegral :
      (∫ x : α, M / 2 + (R - M / 2) *
          P.indicator (fun _ => (1 : ℝ)) x ∂μ) =
        M / 2 + (R - M / 2) * Measure.real μ P := by
    rw [integral_add hConstI hMulI, integral_const_mul,
      integral_indicator_const (1 : ℝ) hP]
    simp
  have hBudget : M ≤ M / 2 + (R - M / 2) * Measure.real μ P := by
    have h := integral_mono hI hUpperI hPoint
    rw [hIntegral] at h
    exact h
  have hFloor : M / (2 * R - M) ≤ Measure.real μ P := by
    apply (div_le_iff₀ hDen).mpr
    nlinarith [hBudget]
  exact ⟨hDen, hFloor⟩

end

end MGAP4D.MathlibAnalytic.CompactPositiveMomentTail

#print axioms MGAP4D.MathlibAnalytic.CompactPositiveMomentTail.half_mean_upper_tail
