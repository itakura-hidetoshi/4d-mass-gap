import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonNormalizedCharacterEnergy

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

noncomputable def normalized_character_wilson_weak_limit_compile_smoke
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional)
    (H : E.PeriodicHypercubicPlaquetteFamily)
    (W : E.WilsonNormalizedCharacterEnergyFamily)
    (D : E.WilsonActionControlsFunctional
      Phi H.reciprocalPlaquetteScale (fun _ : ℕ => (0 : ENNReal))) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  continuous_compact_gauge_wilson_weak_limit_of_periodicHypercubicNormalizedCharacter
    E Phi H W D

end

end MathlibAnalytic
end MGAP4D
