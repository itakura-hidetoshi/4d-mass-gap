import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonLocalAction

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

def CompactOrientedGaugeWilsonSystem.targetRemotePlaquetteAction
    (L : CompactOrientedGaugeWilsonSystem)
    (A : L.Configuration)
    (target : L.geometry.Edge) : ℝ := by
  classical
  exact ∑ p : L.geometry.Plaquette,
    if L.PlaquetteTouchesEdge p target then 0
    else L.plaquetteEnergy (L.plaquetteHolonomy A p)

theorem compact_oriented_wilsonAction_eq_targetLocal_add_targetRemote
    (L : CompactOrientedGaugeWilsonSystem)
    (A : L.Configuration)
    (target : L.geometry.Edge) :
    L.wilsonAction A =
      L.targetLocalPlaquetteAction A target +
        L.targetRemotePlaquetteAction A target := by
  classical
  unfold CompactOrientedGaugeWilsonSystem.wilsonAction
    CompactOrientedGaugeWilsonSystem.targetLocalPlaquetteAction
    CompactOrientedGaugeWilsonSystem.targetRemotePlaquetteAction
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases h : L.PlaquetteTouchesEdge p target <;> simp [h]

theorem compact_oriented_replaceLink_boundary_eq_of_not_touches_target
    (L : CompactOrientedGaugeWilsonSystem)
    (A : L.Configuration)
    (target : L.geometry.Edge)
    (g h : L.Gauge)
    (p : L.geometry.Plaquette)
    (hNotTouch : ¬ L.PlaquetteTouchesEdge p target)
    (k : Fin 4) :
    L.replaceLink A target g (L.geometry.boundary p k).edge =
      L.replaceLink A target h (L.geometry.boundary p k).edge := by
  have hBoundary : (L.geometry.boundary p k).edge ≠ target := by
    intro hk
    exact hNotTouch ⟨k, hk⟩
  simp [CompactOrientedGaugeWilsonSystem.replaceLink, hBoundary]

theorem compact_oriented_plaquetteHolonomy_replaceLink_eq_of_not_touches_target
    (L : CompactOrientedGaugeWilsonSystem)
    (A : L.Configuration)
    (target : L.geometry.Edge)
    (g h : L.Gauge)
    (p : L.geometry.Plaquette)
    (hNotTouch : ¬ L.PlaquetteTouchesEdge p target) :
    L.plaquetteHolonomy (L.replaceLink A target g) p =
      L.plaquetteHolonomy (L.replaceLink A target h) p := by
  apply compact_oriented_plaquetteHolonomy_congr
  intro k
  exact compact_oriented_replaceLink_boundary_eq_of_not_touches_target
    L A target g h p hNotTouch k

end
end MathlibAnalytic
end MGAP4D
