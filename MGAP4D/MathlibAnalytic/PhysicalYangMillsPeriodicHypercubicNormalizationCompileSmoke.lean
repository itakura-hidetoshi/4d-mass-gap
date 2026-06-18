import MGAP4D.MathlibAnalytic.PhysicalYangMillsPeriodicHypercubicNormalization

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

noncomputable def periodic_hypercubic_wilson_weak_limit_compile_smoke
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional)
    (scale offset : ℕ → ENNReal)
    (H : E.PeriodicHypercubicPlaquetteFamily)
    (V : E.WilsonPeriodicHypercubicScaledVolumeBound scale H)
    (M : E.WilsonCompactEnergyMaximumUniformBound)
    (O : WilsonOffsetUniformBound offset)
    (D : E.WilsonActionControlsFunctional Phi scale offset) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  continuous_compact_gauge_wilson_weak_limit_of_periodicHypercubicBounds
    E Phi scale offset H V M O D

noncomputable def periodic_hypercubic_reciprocal_wilson_weak_limit_compile_smoke
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional)
    (offset : ℕ → ENNReal)
    (H : E.PeriodicHypercubicPlaquetteFamily)
    (M : E.WilsonCompactEnergyMaximumUniformBound)
    (O : WilsonOffsetUniformBound offset)
    (D : E.WilsonActionControlsFunctional
      Phi H.reciprocalPlaquetteScale offset) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  continuous_compact_gauge_wilson_weak_limit_of_periodicHypercubicReciprocalScale
    E Phi offset H M O D

end

end MathlibAnalytic
end MGAP4D
