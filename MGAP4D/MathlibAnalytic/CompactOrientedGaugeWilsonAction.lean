import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonAlgebra

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Wilson action on physical positive links with signed boundary traversal. -/
def CompactOrientedGaugeWilsonSystem.wilsonAction
    (L : CompactOrientedGaugeWilsonSystem)
    (A : L.Configuration) : ℝ :=
  ∑ p : L.geometry.Plaquette,
    L.plaquetteEnergy (L.plaquetteHolonomy A p)

/-- Nonnegativity of the compact oriented Wilson action. -/
theorem compact_oriented_wilsonAction_nonneg
    (L : CompactOrientedGaugeWilsonSystem)
    (A : L.Configuration) :
    0 ≤ L.wilsonAction A := by
  unfold CompactOrientedGaugeWilsonSystem.wilsonAction
  exact Finset.sum_nonneg fun p _ => L.plaquetteEnergy_nonneg _

/-- Gauge invariance of the compact oriented Wilson action. -/
theorem compact_oriented_wilsonAction_gaugeInvariant
    (L : CompactOrientedGaugeWilsonSystem)
    (gamma : L.GaugeTransformation)
    (A : L.Configuration) :
    L.wilsonAction (L.gaugeTransform gamma A) = L.wilsonAction A := by
  unfold CompactOrientedGaugeWilsonSystem.wilsonAction
  apply Finset.sum_congr rfl
  intro p _hp
  rw [compact_oriented_plaquetteHolonomy_gaugeTransform]
  exact L.plaquetteEnergy_conjInvariant _ _

end

end MathlibAnalytic
end MGAP4D
