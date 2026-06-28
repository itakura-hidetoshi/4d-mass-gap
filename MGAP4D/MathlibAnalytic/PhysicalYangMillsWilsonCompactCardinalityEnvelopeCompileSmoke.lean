import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonCompactCardinalityEnvelope

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

noncomputable def compact_wilson_weak_limit_of_cardinality_envelope_compile_smoke
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional)
    (scale offset : ℕ → ENNReal)
    (N : E.WilsonCompactPlaquetteCardinalityEnvelope scale offset)
    (D : E.WilsonActionControlsFunctional Phi scale offset) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  continuous_compact_gauge_wilson_weak_limit_of_compactPlaquetteCardinalityEnvelope
    E Phi scale offset N D

end

end MathlibAnalytic
end MGAP4D
