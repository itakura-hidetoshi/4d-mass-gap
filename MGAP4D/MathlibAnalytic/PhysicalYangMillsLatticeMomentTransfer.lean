import MGAP4D.MathlibAnalytic.PhysicalYangMillsCompactContainment
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Change of variables for the interpolated lattice probability law. -/
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
