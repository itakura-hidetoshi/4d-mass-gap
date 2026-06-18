import MGAP4D.MathlibAnalytic.PhysicalYangMillsCompactContainmentLimit

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Set

noncomputable section

/-- Compile gate for the quantitative compact-core data. -/
theorem physical_compact_containment_tail_compile_smoke
    {E : PhysicalFourDimensionalYangMillsLatticeEmbedding}
    (C : PhysicalYangMillsUniformCompactContainment E) :
    Tendsto C.tailBound atTop (nhds 0) :=
  C.tailBound_tendsto_zero

/-- Compile gate for the uniform complement-mass estimate. -/
theorem physical_compact_containment_bound_compile_smoke
    {E : PhysicalFourDimensionalYangMillsLatticeEmbedding}
    (C : PhysicalYangMillsUniformCompactContainment E)
    (latticeScale compactScale : ℕ) :
    E.embeddedMeasure latticeScale (C.compactCore compactScale)ᶜ ≤
      C.tailBound compactScale :=
  C.measure_compl_le latticeScale compactScale

end

end MathlibAnalytic
end MGAP4D
