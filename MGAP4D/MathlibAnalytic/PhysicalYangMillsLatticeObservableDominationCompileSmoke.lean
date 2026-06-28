import MGAP4D.MathlibAnalytic.PhysicalYangMillsLatticeObservableDomination

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Compile gate for generic lattice-observable domination. -/
noncomputable def physical_weak_limit_of_observable_domination_compile_smoke
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding)
    (Phi : E.PhysicalCoerciveFunctional)
    (O : E.LatticeObservableMomentBound)
    (D : E.LatticeObservableDominatesFunctional Phi O) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  D.toWeakLimit

/-- Compile gate for continuous compact-gauge Wilson observable domination. -/
noncomputable def compact_wilson_weak_limit_of_observable_domination_compile_smoke
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional)
    (O : E.LatticeObservableMomentBound)
    (D : E.LatticeObservableDominatesFunctional Phi O) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  continuous_compact_gauge_wilson_weak_limit_of_latticeObservableDomination
    E Phi O D

end

end MathlibAnalytic
end MGAP4D
