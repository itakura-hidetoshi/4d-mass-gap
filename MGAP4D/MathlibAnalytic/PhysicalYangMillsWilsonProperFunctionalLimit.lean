import MGAP4D.MathlibAnalytic.PhysicalYangMillsProperCoerciveFunctional
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonNormalizedActionBound

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Exact periodic four-dimensional geometry, normalized-character Wilson energy,
and one proper physical functional controlled by the reciprocal-volume action
produce a physical continuum weak limit. -/
noncomputable def
    continuous_compact_gauge_wilson_weak_limit_of_periodicHypercubicProperFunctional
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
    PhysicalFourDimensionalYangMillsWeakLimit := by
  let Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional :=
    E.physicalCoerciveFunctional_ofProper functional functional_proper
  let D : E.WilsonActionControlsFunctional
      Phi H.reciprocalPlaquetteScale (fun _ : ℕ => (0 : ENNReal)) :=
    { pointwise_le := functional_le_action }
  exact continuous_compact_gauge_wilson_weak_limit_of_normalizedCharacterActionBound
    E Phi H W D

end

end MathlibAnalytic
end MGAP4D
