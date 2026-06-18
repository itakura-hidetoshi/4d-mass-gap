import MGAP4D.MathlibAnalytic.PhysicalYangMillsCompactContainment
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Change of variables for the interpolated lattice probability law.

This removes a separate pushforward-moment hypothesis: an estimate for
`f (E.interpolate n u)` under the original lattice law is exactly the
corresponding estimate for `f` under the embedded law. -/
theorem PhysicalFourDimensionalYangMillsLatticeEmbedding.lintegral_embeddedMeasure
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding)
    (f : E.PhysicalConfiguration → ENNReal)
    (hf : Measurable f)
    (n : ℕ) :
    ∫⁻ x, f x ∂(E.embeddedMeasure n : Measure E.PhysicalConfiguration) =
      ∫⁻ u, f (E.interpolate n u)
        ∂(E.latticeMeasure n : Measure (E.LatticeConfiguration n)) := by
  change
    ∫⁻ x, f x ∂Measure.map (E.interpolate n)
        (E.latticeMeasure n : Measure (E.LatticeConfiguration n)) = _
  exact MeasureTheory.lintegral_map hf (E.interpolate_measurable n)

end

end MathlibAnalytic
end MGAP4D
