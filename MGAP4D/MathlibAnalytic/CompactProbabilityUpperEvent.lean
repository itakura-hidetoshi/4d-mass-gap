import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# Probability mass of a genuine upper event

A bounded integrable observable is compared with a constant plus the indicator
of its actual upper event. No replacement measure, density or moment is used.
-/
namespace MGAP4D.MathlibAnalytic.CompactProbabilityUpperEvent
open MeasureTheory
noncomputable section
set_option autoImplicit false
variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) [IsProbabilityMeasure μ]

/-- A first-moment lower bound on the mass of the actual upper event. -/
theorem mean_sub_threshold_le_cap_mul_mass
    (f : X → ℝ) (hf : Integrable f μ) (t K : ℝ) (ht : 0 ≤ t)
    (hcap : ∀ x, f x ≤ K) (hS : MeasurableSet {x | t < f x}) :
    (∫ x, f x ∂μ) - t ≤ K * Measure.real μ {x | t < f x} := by
  let S : Set X := {x | t < f x}
  have hI : Integrable (S.indicator (fun _ : X => K)) μ :=
    (integrable_const K).indicator hS
  have hpoint (x : X) : f x ≤ t + S.indicator (fun _ : X => K) x := by
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
      linarith only [hcap x, ht]
    · rw [Set.indicator_of_notMem hx, add_zero]
      exact le_of_not_gt hx
  have hsum : (∫ x, t + S.indicator (fun _ : X => K) x ∂μ) =
      t + Measure.real μ S * K := by
    rw [integral_add (integrable_const t) hI, integral_indicator_const K hS]
    simp [smul_eq_mul]
  have h := integral_mono hf ((integrable_const t).add hI) hpoint
  rw [hsum] at h
  change (∫ x, f x ∂μ) - t ≤ K * Measure.real μ S
  nlinarith only [h]

/-- Half the actual positive mean gives an explicit positive mass certificate.
The cap and the mean may depend on every physical parameter. -/
theorem halfMean_div_cap_le_mass
    (f : X → ℝ) (hf : Integrable f μ) (hm : 0 < ∫ x, f x ∂μ)
    (K : ℝ) (hK : 0 < K) (hcap : ∀ x, f x ≤ K)
    (hS : MeasurableSet {x | (∫ y, f y ∂μ) / 2 < f x}) :
    (∫ x, f x ∂μ) / (2 * K) ≤
      Measure.real μ {x | (∫ y, f y ∂μ) / 2 < f x} := by
  have h := mean_sub_threshold_le_cap_mul_mass μ f hf
    ((∫ x, f x ∂μ) / 2) K (div_nonneg hm.le (by norm_num)) hcap hS
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hK)).mpr
  nlinarith only [h]

end
end MGAP4D.MathlibAnalytic.CompactProbabilityUpperEvent

#print axioms MGAP4D.MathlibAnalytic.CompactProbabilityUpperEvent.mean_sub_threshold_le_cap_mul_mass
#print axioms MGAP4D.MathlibAnalytic.CompactProbabilityUpperEvent.halfMean_div_cap_le_mass
