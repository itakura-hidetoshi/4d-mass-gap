import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonPlaquetteControl

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

noncomputable def compact_wilson_weak_limit_of_plaquette_control_compile_smoke
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional)
    (scale offset : ℕ → ENNReal)
    (B : E.WilsonPlaquetteEnergyUniformBound)
    (N : E.WilsonPlaquetteNormalizationEnvelope scale offset B)
    (D : E.WilsonActionControlsFunctional Phi scale offset) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  continuous_compact_gauge_wilson_weak_limit_of_plaquetteControl
    E Phi scale offset B N D

end

end MathlibAnalytic
end MGAP4D
