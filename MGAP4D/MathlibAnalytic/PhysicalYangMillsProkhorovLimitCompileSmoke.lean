import MGAP4D.MathlibAnalytic.PhysicalYangMillsProkhorovLimit

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Compile gate for Prokhorov extraction from tight lattice laws. -/
theorem physical_prokhorov_subsequence_compile_smoke
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding)
    (hTight : E.IsTight) :
    Nonempty (PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit E) :=
  physical_yang_mills_prokhorov_subsequence_exists E hTight

/-- Compile gate for the resulting physical weak-limit carrier. -/
noncomputable def physical_weak_limit_of_tight_compile_smoke
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding)
    (hTight : E.IsTight) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  physical_yang_mills_weak_limit_of_tight E hTight

/-- Compile gate for the concrete compact-gauge Wilson specialization. -/
noncomputable def compact_wilson_weak_limit_of_tight_compile_smoke
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (hTight : E.toLatticeEmbedding.IsTight) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  continuous_compact_gauge_wilson_weak_limit_of_tight E hTight

end

end MathlibAnalytic
end MGAP4D
