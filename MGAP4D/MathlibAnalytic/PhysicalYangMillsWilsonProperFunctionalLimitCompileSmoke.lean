import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonProperFunctionalLimit
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSpecialUnitaryMatrixTraceFormula
import MGAP4D.MathlibAnalytic.PhysicalYangMillsEvenPeriodicWilsonOSWeakStarReflectionPositivity
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSBilinearForm

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Compile-smoke entry point for the physical Wilson weak-limit spine.

The imports above now include the continuum gauge-invariant OS positive
semidefinite bilinear form generated from the actual even-periodic Wilson laws. -/
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

noncomputable def periodic_wilson_proper_nnreal_functional_weak_limit_compile_smoke
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (H : E.PeriodicHypercubicPlaquetteFamily)
    (W : E.WilsonNormalizedCharacterEnergyFamily)
    (functional : E.PhysicalConfiguration → NNReal)
    (functional_proper : IsProperMap functional)
    (functional_le_action :
      ∀ n U,
        (functional (E.interpolate n U) : ENNReal) ≤
          E.renormalizedWilsonActionObservable
            H.reciprocalPlaquetteScale
            (fun _ : ℕ => (0 : ENNReal)) n U) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  continuous_compact_gauge_wilson_weak_limit_of_periodicHypercubicProperNNRealFunctional
    E H W functional functional_proper functional_le_action

end

end MathlibAnalytic
end MGAP4D
