import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonProperFunctionalLimit

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

noncomputable def periodic_wilson_proper_functional_weak_limit_compile_smoke
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (H : E.PeriodicHypercubicPlaquetteFamily)
    (W : E.WilsonNormalizedCharacterEnergyFamily)
    (functional : E.PhysicalConfiguration → ENNReal)
    (functional_proper : IsProperMap functional)
    (functional_le_action :
      ∀ n U,
        functional (E.interpolate n U) ≤
          E.renormalizedWilsonActionObservable
            H.reciprocalPlaquetteScale
            (fun _ : ℕ => (0 : ENNReal)) n U) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  continuous_compact_gauge_wilson_weak_limit_of_periodicHypercubicProperFunctional
    E H W functional functional_proper functional_le_action

end

end MathlibAnalytic
end MGAP4D
