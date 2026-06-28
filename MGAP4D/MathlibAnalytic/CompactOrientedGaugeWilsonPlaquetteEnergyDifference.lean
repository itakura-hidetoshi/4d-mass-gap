import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonSharedPlaquetteAction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

theorem compact_oriented_sharedPlaquetteEnergyDifference_abs_le
    (L : CompactOrientedGaugeWilsonSystem)
    (energyBound : ℝ)
    (hUpper : ∀ U : L.Gauge, L.plaquetteEnergy U ≤ energyBound)
    (A : L.Configuration)
    (target source : L.geometry.Edge)
    (u g : L.Gauge)
    (p : L.geometry.Plaquette) :
    |L.plaquetteEnergy
          (L.plaquetteHolonomy (L.replaceLink A target u) p) -
        L.plaquetteEnergy
          (L.plaquetteHolonomy
            (L.replaceLink (L.replaceLink A source g) target u) p)| ≤
      energyBound := by
  have hLeft0 := L.plaquetteEnergy_nonneg
    (L.plaquetteHolonomy (L.replaceLink A target u) p)
  have hRight0 := L.plaquetteEnergy_nonneg
    (L.plaquetteHolonomy
      (L.replaceLink (L.replaceLink A source g) target u) p)
  have hLeftUpper := hUpper
    (L.plaquetteHolonomy (L.replaceLink A target u) p)
  have hRightUpper := hUpper
    (L.plaquetteHolonomy
      (L.replaceLink (L.replaceLink A source g) target u) p)
  apply abs_sub_le_iff.mpr
  constructor <;> linarith

end
end MathlibAnalytic
end MGAP4D
