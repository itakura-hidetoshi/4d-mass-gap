import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonActionDecomposition

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

theorem compact_oriented_targetRemotePlaquetteAction_replaceLink_eq
    (L : CompactOrientedGaugeWilsonSystem)
    (A : L.Configuration)
    (target : L.geometry.Edge)
    (g h : L.Gauge) :
    L.targetRemotePlaquetteAction (L.replaceLink A target g) target =
      L.targetRemotePlaquetteAction (L.replaceLink A target h) target := by
  classical
  unfold CompactOrientedGaugeWilsonSystem.targetRemotePlaquetteAction
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hTouch : L.PlaquetteTouchesEdge p target
  · simp [hTouch]
  · simp only [if_neg hTouch]
    rw [compact_oriented_plaquetteHolonomy_replaceLink_eq_of_not_touches_target
      L A target g h p hTouch]

theorem compact_oriented_targetRemotePlaquetteAction_replaceLink
    (L : CompactOrientedGaugeWilsonSystem)
    (A : L.Configuration)
    (target : L.geometry.Edge)
    (g : L.Gauge) :
    L.targetRemotePlaquetteAction (L.replaceLink A target g) target =
      L.targetRemotePlaquetteAction A target := by
  calc
    L.targetRemotePlaquetteAction (L.replaceLink A target g) target =
        L.targetRemotePlaquetteAction
          (L.replaceLink A target (A target)) target :=
      compact_oriented_targetRemotePlaquetteAction_replaceLink_eq
        L A target g (A target)
    _ = L.targetRemotePlaquetteAction A target := by
      rw [compact_oriented_replaceLink_current]

theorem compact_oriented_wilsonAction_replaceLink_eq_local_add_remote
    (L : CompactOrientedGaugeWilsonSystem)
    (A : L.Configuration)
    (target : L.geometry.Edge)
    (g : L.Gauge) :
    L.wilsonAction (L.replaceLink A target g) =
      L.targetLocalPlaquetteAction (L.replaceLink A target g) target +
        L.targetRemotePlaquetteAction A target := by
  rw [compact_oriented_wilsonAction_eq_targetLocal_add_targetRemote,
    compact_oriented_targetRemotePlaquetteAction_replaceLink]

end
end MathlibAnalytic
end MGAP4D
