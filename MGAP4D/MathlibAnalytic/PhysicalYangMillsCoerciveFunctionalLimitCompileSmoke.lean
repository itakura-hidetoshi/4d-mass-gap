import MGAP4D.MathlibAnalytic.PhysicalYangMillsCoerciveFunctionalLimit

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Compile gate for separated physical compactness and embedded-law moments. -/
noncomputable def physical_weak_limit_of_functional_moment_compile_smoke
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding)
    (Phi : E.PhysicalCoerciveFunctional)
    (M : UniformCoerciveFunctionalMomentBound Phi E.embeddedMeasureSet) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  physical_yang_mills_weak_limit_of_coerciveFunctionalMomentBound E Phi M

/-- Compile gate for separated physical compactness and original-lattice
moments. -/
noncomputable def physical_weak_limit_of_lattice_functional_moment_compile_smoke
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding)
    (Phi : E.PhysicalCoerciveFunctional)
    (M : E.LatticeCoerciveFunctionalMomentBound Phi) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  physical_yang_mills_weak_limit_of_latticeCoerciveFunctionalMomentBound E Phi M

/-- Compile gate for the compact-gauge Wilson common-carrier route. -/
noncomputable def compact_wilson_weak_limit_of_functional_moment_compile_smoke
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional)
    (M : UniformCoerciveFunctionalMomentBound
      Phi E.toLatticeEmbedding.embeddedMeasureSet) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  continuous_compact_gauge_wilson_weak_limit_of_coerciveFunctionalMomentBound
    E Phi M

/-- Compile gate for the compact-gauge Wilson original-Gibbs-law route. -/
noncomputable def compact_wilson_weak_limit_of_lattice_functional_moment_compile_smoke
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional)
    (M : E.toLatticeEmbedding.LatticeCoerciveFunctionalMomentBound Phi) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  continuous_compact_gauge_wilson_weak_limit_of_latticeCoerciveFunctionalMomentBound
    E Phi M

end

end MathlibAnalytic
end MGAP4D
