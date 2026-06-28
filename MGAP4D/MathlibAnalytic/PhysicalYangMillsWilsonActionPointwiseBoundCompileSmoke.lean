import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonActionPointwiseBound

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

noncomputable def compact_wilson_weak_limit_of_action_pointwise_bound_compile_smoke
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional)
    (scale offset : ℕ → ENNReal)
    (B : E.WilsonActionUniformPointwiseBound)
    (C : WilsonActionAffineCoefficientBounds scale offset)
    (D : E.WilsonActionControlsFunctional Phi scale offset) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  continuous_compact_gauge_wilson_weak_limit_of_actionPointwiseBound
    E Phi scale offset B C D

end

end MathlibAnalytic
end MGAP4D
