import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped ENNReal

noncomputable section

universe u v

/-- The first marginal of a density with respect to a product reference law is
the first reference measure weighted by the fiberwise `lintegral` of that
density. -/
theorem measure_map_fst_prod_withDensity
    {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν]
    (ρ : α × β → ℝ≥0∞)
    (hρ : Measurable ρ) :
    Measure.map Prod.fst ((μ.prod ν).withDensity ρ) =
      μ.withDensity (fun x => ∫⁻ y, ρ (x, y) ∂ν) := by
  ext s hs
  rw [Measure.map_apply measurable_fst hs]
  rw [withDensity_apply _ (hs.preimage measurable_fst)]
  rw [withDensity_apply _ hs]
  rw [← lintegral_indicator (hs.preimage measurable_fst)]
  rw [← lintegral_indicator hs]
  rw [MeasureTheory.lintegral_prod]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_not_mem hx]

end

end MathlibAnalytic
end MGAP4D
