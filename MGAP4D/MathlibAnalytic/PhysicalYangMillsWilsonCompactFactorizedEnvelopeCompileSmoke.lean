import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonCompactFactorizedEnvelope

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

noncomputable def compact_wilson_weak_limit_of_factorized_bounds_compile_smoke
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional)
    (scale offset : ℕ → ENNReal)
    (C : E.WilsonScaledPlaquetteCardinalityBound scale)
    (M : E.WilsonCompactEnergyMaximumUniformBound)
    (O : WilsonOffsetUniformBound offset)
    (D : E.WilsonActionControlsFunctional Phi scale offset) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  continuous_compact_gauge_wilson_weak_limit_of_compactPlaquetteFactorizedBounds
    E Phi scale offset C M O D

end

end MathlibAnalytic
end MGAP4D
