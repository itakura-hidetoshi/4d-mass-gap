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

/-- Compile gate for subsequential continuum-measure existence. -/
theorem physical_compact_containment_subsequence_compile_smoke
    {E : PhysicalFourDimensionalYangMillsLatticeEmbedding}
    (C : PhysicalYangMillsUniformCompactContainment E) :
    Nonempty (PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit E) :=
  physical_yang_mills_subsequence_exists_of_compact_containment C

/-- Compile gate for the physical weak-limit carrier. -/
noncomputable def physical_compact_containment_weak_limit_compile_smoke
    {E : PhysicalFourDimensionalYangMillsLatticeEmbedding}
    (C : PhysicalYangMillsUniformCompactContainment E) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  physical_yang_mills_weak_limit_of_compact_containment C

end

end MathlibAnalytic
end MGAP4D
