import MGAP4D.MathlibAnalytic.PhysicalYangMillsCompactContainmentLimit

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Set

noncomputable section

theorem physical_compact_core_tail_compile_smoke
    {E : PhysicalFourDimensionalYangMillsLatticeEmbedding}
    (C : PhysicalYangMillsCompactCoreScale E) :
    Tendsto C.tailBound atTop (nhds 0) :=
  C.tailBound_tendsto_zero

end
end MathlibAnalytic
end MGAP4D
