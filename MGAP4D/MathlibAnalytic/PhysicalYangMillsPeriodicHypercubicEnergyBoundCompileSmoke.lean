import MGAP4D.MathlibAnalytic.PhysicalYangMillsPeriodicHypercubicEnergyBound

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

noncomputable def periodic_hypercubic_energy_bound_weak_limit_compile_smoke
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional)
    (H : E.PeriodicHypercubicPlaquetteFamily)
    (B : E.WilsonPlaquetteEnergyUniformBound)
    (D : E.WilsonActionControlsFunctional
      Phi H.reciprocalPlaquetteScale (fun _ : ℕ => (0 : ENNReal))) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  continuous_compact_gauge_wilson_weak_limit_of_periodicHypercubicEnergyBound
    E Phi H B D

end

end MathlibAnalytic
end MGAP4D
