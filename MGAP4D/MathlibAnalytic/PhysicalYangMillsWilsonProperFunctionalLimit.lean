import MGAP4D.MathlibAnalytic.PhysicalYangMillsProperCoerciveFunctional
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonNormalizedActionBound

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Exact periodic geometry, normalized-character Wilson energy, and one proper
`ENNReal`-valued physical functional produce a weak limit. Since `ENNReal` is
compact, this constructor is mainly useful for compact physical carriers. -/
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

/-- Exact periodic geometry, normalized-character Wilson energy, and one proper
`NNReal`-valued physical functional controlled by the reciprocal-volume action
produce a physical weak limit on a possibly noncompact physical carrier. -/
noncomputable def
    continuous_compact_gauge_wilson_weak_limit_of_periodicHypercubicProperNNRealFunctional
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
    PhysicalFourDimensionalYangMillsWeakLimit := by
  let Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional :=
    E.physicalCoerciveFunctional_ofProperNNReal functional functional_proper
  let D : E.WilsonActionControlsFunctional
      Phi H.reciprocalPlaquetteScale (fun _ : ℕ => (0 : ENNReal)) :=
    { pointwise_le := functional_le_action }
  exact continuous_compact_gauge_wilson_weak_limit_of_normalizedCharacterActionBound
    E Phi H W D

end

end MathlibAnalytic
end MGAP4D
