import MGAP4D.MathlibAnalytic.PhysicalYangMillsLatticeEmbedding

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

/-- Compile gate for pushing varying lattice laws into one physical carrier. -/
theorem physical_lattice_embedded_probability_compile_smoke
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding)
    (n : ℕ) :
    IsProbabilityMeasure (E.embeddedMeasure n : Measure E.PhysicalConfiguration) := by
  infer_instance

/-- Compile gate for constructing the physical weak-limit carrier from a generic
lattice interpolation sequence. -/
noncomputable def physical_lattice_toWeakLimit_compile_smoke
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding)
    (continuumMeasure : ProbabilityMeasure E.PhysicalConfiguration)
    (hWeak : Tendsto E.embeddedMeasure atTop (nhds continuumMeasure)) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  E.toWeakLimit continuumMeasure hWeak

/-- Compile gate for the concrete compact-gauge Wilson interpolation route. -/
noncomputable def compact_wilson_physical_toWeakLimit_compile_smoke
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (continuumMeasure : ProbabilityMeasure E.PhysicalConfiguration)
    (hWeak :
      Tendsto E.toLatticeEmbedding.embeddedMeasure atTop
        (nhds continuumMeasure)) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  E.toWeakLimit continuumMeasure hWeak

end

end MathlibAnalytic
end MGAP4D
