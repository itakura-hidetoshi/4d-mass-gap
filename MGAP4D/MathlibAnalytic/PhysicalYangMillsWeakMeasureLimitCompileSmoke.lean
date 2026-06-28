import MGAP4D.MathlibAnalytic.PhysicalYangMillsWeakMeasureLimit

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

/-- Compile gate for the actual continuum probability carrier. -/
theorem physical_weak_limit_probability_compile_smoke
    (S : PhysicalFourDimensionalYangMillsWeakLimit) :
    IsProbabilityMeasure S.measure :=
  physical_yang_mills_weak_limit_isProbabilityMeasure S

/-- Compile gate for bounded-continuous observable convergence. -/
theorem physical_weak_limit_expectation_compile_smoke
    (S : PhysicalFourDimensionalYangMillsWeakLimit)
    (O : BoundedContinuousFunction S.Configuration ℝ) :
    Tendsto
      (fun n : ℕ =>
        ∫ A, O A ∂(S.approximatingMeasure n : Measure S.Configuration))
      atTop
      (nhds
        (∫ A, O A ∂(S.continuumMeasure : Measure S.Configuration))) :=
  physical_yang_mills_bounded_observable_expectation_converges S O

/-- Compile gate for automatic symmetry transfer to the weak limit. -/
theorem physical_weak_limit_symmetry_compile_smoke
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (g : S.Symmetry) :
    S.continuumMeasure.map
        (S.action_continuous g).measurable.aemeasurable =
      S.continuumMeasure :=
  physical_yang_mills_symmetry_passes_to_weak_limit S g

end

end MathlibAnalytic
end MGAP4D
