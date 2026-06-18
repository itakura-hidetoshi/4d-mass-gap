import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonActionExpectation

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

noncomputable def compact_wilson_weak_limit_of_action_moment_compile_smoke
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional)
    (scale offset : ℕ → ENNReal)
    (C : WilsonActionAffineCoefficientBounds scale offset)
    (M : E.WilsonActionMomentBound)
    (D : E.WilsonActionControlsFunctional Phi scale offset) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  continuous_compact_gauge_wilson_weak_limit_of_actionMoment
    E Phi scale offset C M D

end

end MathlibAnalytic
end MGAP4D
