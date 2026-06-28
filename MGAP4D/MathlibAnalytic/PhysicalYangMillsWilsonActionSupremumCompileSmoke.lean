import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonActionSupremum

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

noncomputable def compact_wilson_weak_limit_of_action_supremum_compile_smoke
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional)
    (scale offset : ℕ → ENNReal)
    (D : E.WilsonActionControlsFunctional Phi scale offset)
    (S : E.WilsonActionControlFiniteSupremum scale offset) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  continuous_compact_gauge_wilson_weak_limit_of_actionExpectationSupremum
    E Phi scale offset D S

end

end MathlibAnalytic
end MGAP4D
