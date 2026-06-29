import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonLocalHolonomy

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

def CompactOrientedGaugeWilsonSystem.targetLocalPlaquetteAction
    (L : CompactOrientedGaugeWilsonSystem)
    (A : L.Configuration)
    (target : L.geometry.Edge) : ℝ := by
  classical
  exact ∑ p : L.geometry.Plaquette,
    if L.PlaquetteTouchesEdge p target then
      L.plaquetteEnergy (L.plaquetteHolonomy A p)
    else 0

theorem compact_oriented_targetLocalPlaquetteAction_replaceLink_eq_of_not_neighbor
    (L : CompactOrientedGaugeWilsonSystem)
    (A B : L.Configuration)
    (target source : L.geometry.Edge)
    (g : L.Gauge)
    (hNotNeighbor : source ∉ L.plaquetteNeighbors target)
    (hAgree : L.AgreeOffLink A B source) :
    L.targetLocalPlaquetteAction (L.replaceLink A target g) target =
      L.targetLocalPlaquetteAction (L.replaceLink B target g) target := by
  classical
  unfold CompactOrientedGaugeWilsonSystem.targetLocalPlaquetteAction
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hTarget : L.PlaquetteTouchesEdge p target
  · simp only [if_pos hTarget]
    rw [compact_oriented_local_holonomy_eq
      L A B target source g p hTarget hNotNeighbor hAgree]
  · simp [hTarget]

end
end MathlibAnalytic
end MGAP4D
