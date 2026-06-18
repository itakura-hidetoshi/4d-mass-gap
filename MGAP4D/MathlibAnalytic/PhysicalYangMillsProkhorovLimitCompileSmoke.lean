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

/-- Compile gate for quantitative compact containment. -/
noncomputable def physical_weak_limit_of_compact_containment_compile_smoke
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding)
    (C : E.CompactContainmentCertificate) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  physical_yang_mills_weak_limit_of_compactContainment E C

/-- Compile gate for the common-carrier coercive-moment route. -/
noncomputable def physical_weak_limit_of_coercive_moment_compile_smoke
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding)
    (C : E.CoerciveMomentCertificate) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  physical_yang_mills_weak_limit_of_coerciveMoment E C

/-- Compile gate for the original-lattice moment route. -/
noncomputable def physical_weak_limit_of_lattice_moment_compile_smoke
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding)
    (C : E.LatticeCoerciveMomentCertificate) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  physical_yang_mills_weak_limit_of_latticeCoerciveMoment E C

/-- Compile gate for the concrete compact-gauge Wilson specialization. -/
noncomputable def compact_wilson_weak_limit_of_tight_compile_smoke
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (hTight : E.toLatticeEmbedding.IsTight) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  continuous_compact_gauge_wilson_weak_limit_of_tight E hTight

/-- Compile gate for Wilson compact containment. -/
noncomputable def compact_wilson_weak_limit_of_compact_containment_compile_smoke
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (C : E.toLatticeEmbedding.CompactContainmentCertificate) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  continuous_compact_gauge_wilson_weak_limit_of_compactContainment E C

/-- Compile gate for Wilson common-carrier coercive moments. -/
noncomputable def compact_wilson_weak_limit_of_coercive_moment_compile_smoke
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (C : E.toLatticeEmbedding.CoerciveMomentCertificate) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  continuous_compact_gauge_wilson_weak_limit_of_coerciveMoment E C

/-- Compile gate for Wilson finite-lattice coercive moments. -/
noncomputable def compact_wilson_weak_limit_of_lattice_moment_compile_smoke
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (C : E.toLatticeEmbedding.LatticeCoerciveMomentCertificate) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  continuous_compact_gauge_wilson_weak_limit_of_latticeCoerciveMoment E C

end

end MathlibAnalytic
end MGAP4D
