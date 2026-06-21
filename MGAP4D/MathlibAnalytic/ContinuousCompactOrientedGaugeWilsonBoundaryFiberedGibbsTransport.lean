import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonBoundaryFiberedHaarFactorization
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonSystem
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace MeasurableEquiv

/-- Transport of a measurable density through a measurable equivalence. -/
theorem map_withDensity_comp_symm_transport
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (f : α → ℝ≥0∞)
    (hf : Measurable f) :
    Measure.map e (μ.withDensity f) =
      (Measure.map e μ).withDensity (fun y => f (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs]
  rw [withDensity_apply _ (hs.preimage e.measurable)]
  rw [withDensity_apply _ hs]
  have hMap := setLIntegral_map (μ := μ) (g := (e : α → β)) hs
    (hf.comp e.symm.measurable) e.measurable
  simpa using hMap.symm

end MeasurableEquiv

end

end MathlibAnalytic
end MGAP4D
