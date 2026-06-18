import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonPlaquetteLocality

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The part of the Wilson action contributed by plaquettes not touching the
selected target link. -/
def FiniteLatticeWilsonSystem.targetRemotePlaquetteAction
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge) : ℝ := by
  classical
  exact ∑ p : L.Plaquette,
    if L.PlaquetteTouchesEdge p target then 0
    else L.plaquetteEnergy (L.plaquetteHolonomy A p)

/-- The Wilson action splits exactly into target-local and target-remote
plaquette contributions. -/
theorem finite_lattice_wilsonAction_eq_targetLocal_add_targetRemote
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge) :
    L.wilsonAction A =
      L.targetLocalPlaquetteAction A target +
        L.targetRemotePlaquetteAction A target := by
  classical
  unfold FiniteLatticeWilsonSystem.wilsonAction
    FiniteLatticeWilsonSystem.targetLocalPlaquetteAction
    FiniteLatticeWilsonSystem.targetRemotePlaquetteAction
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hTouch : L.PlaquetteTouchesEdge p target
  · simp [hTouch]
  · simp [hTouch]

/-- A plaquette not touching `target` has the same boundary values after any two
replacements of `target`. -/
theorem finite_lattice_replaceLink_boundary_eq_of_not_touches_target
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge)
    (g h : L.Gauge)
    (p : L.Plaquette)
    (hNotTouch : ¬ L.PlaquetteTouchesEdge p target)
    (k : Fin 4) :
    L.replaceLink A target g (L.boundary p k) =
      L.replaceLink A target h (L.boundary p k) := by
  classical
  have hBoundary : L.boundary p k ≠ target := by
    intro hk
    exact hNotTouch ⟨k, hk⟩
  simp [FiniteLatticeWilsonSystem.replaceLink, hBoundary]

/-- Remote plaquette holonomy does not depend on the value inserted at the
target link. -/
theorem finite_lattice_plaquetteHolonomy_replaceLink_eq_of_not_touches_target
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge)
    (g h : L.Gauge)
    (p : L.Plaquette)
    (hNotTouch : ¬ L.PlaquetteTouchesEdge p target) :
    L.plaquetteHolonomy (L.replaceLink A target g) p =
      L.plaquetteHolonomy (L.replaceLink A target h) p := by
  apply finite_lattice_plaquetteHolonomy_congr
  intro k
  exact finite_lattice_replaceLink_boundary_eq_of_not_touches_target
    L A target g h p hNotTouch k

/-- The target-remote action is independent of the target replacement value. -/
theorem finite_lattice_targetRemotePlaquetteAction_replaceLink_eq
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge)
    (g h : L.Gauge) :
    L.targetRemotePlaquetteAction (L.replaceLink A target g) target =
      L.targetRemotePlaquetteAction (L.replaceLink A target h) target := by
  classical
  unfold FiniteLatticeWilsonSystem.targetRemotePlaquetteAction
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hTouch : L.PlaquetteTouchesEdge p target
  · simp [hTouch]
  · simp only [if_neg hTouch]
    rw [finite_lattice_plaquetteHolonomy_replaceLink_eq_of_not_touches_target
      L A target g h p hTouch]

/-- Replacing the target by its current value identifies the remote action of
any target replacement with the remote action of the original configuration. -/
theorem finite_lattice_targetRemotePlaquetteAction_replaceLink
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge)
    (g : L.Gauge) :
    L.targetRemotePlaquetteAction (L.replaceLink A target g) target =
      L.targetRemotePlaquetteAction A target := by
  calc
    L.targetRemotePlaquetteAction (L.replaceLink A target g) target =
        L.targetRemotePlaquetteAction
          (L.replaceLink A target (A target)) target :=
      finite_lattice_targetRemotePlaquetteAction_replaceLink_eq
        L A target g (A target)
    _ = L.targetRemotePlaquetteAction A target := by
      rw [finite_lattice_replaceLink_current]

/-- The action of a target-updated configuration is its target-local action plus
a target-independent remote constant. -/
theorem finite_lattice_wilsonAction_replaceLink_eq_local_add_remote
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge)
    (g : L.Gauge) :
    L.wilsonAction (L.replaceLink A target g) =
      L.targetLocalPlaquetteAction (L.replaceLink A target g) target +
        L.targetRemotePlaquetteAction A target := by
  rw [finite_lattice_wilsonAction_eq_targetLocal_add_targetRemote,
    finite_lattice_targetRemotePlaquetteAction_replaceLink]

end

end MathlibAnalytic
end MGAP4D
