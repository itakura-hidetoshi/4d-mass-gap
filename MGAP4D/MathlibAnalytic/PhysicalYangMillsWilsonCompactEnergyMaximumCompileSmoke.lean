import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonCompactEnergyMaximum

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

noncomputable def compact_wilson_weak_limit_of_compact_energy_maximum_compile_smoke
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional)
    (scale offset : ℕ → ENNReal)
    (N : E.WilsonCompactPlaquetteNormalizationEnvelope scale offset)
    (D : E.WilsonActionControlsFunctional Phi scale offset) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  continuous_compact_gauge_wilson_weak_limit_of_compactPlaquetteEnvelope
    E Phi scale offset N D

end

end MathlibAnalytic
end MGAP4D
