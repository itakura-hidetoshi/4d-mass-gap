import MGAP4D.MathlibAnalytic.PhysicalYangMillsCompactContainmentLimit

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Compile gate for compactness of the quantitative Prokhorov class. -/
theorem physical_compact_containment_set_compile_smoke
    {E : PhysicalFourDimensionalYangMillsLatticeEmbedding}
    (C : PhysicalYangMillsUniformCompactContainment E) :
    IsCompact
      {μ : ProbabilityMeasure E.PhysicalConfiguration |
        ∀ m, μ (C.compactCore m)ᶜ ≤ C.tailBound m} :=
  physical_yang_mills_compact_containment_measure_set_isCompact C

end

end MathlibAnalytic
end MGAP4D
