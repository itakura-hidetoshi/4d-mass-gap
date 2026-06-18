import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonSystem

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Replace one physical link value in an orientation-correct configuration. -/
def FiniteOrientedLatticeWilsonSystem.replaceLink
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge)
    (g : L.Gauge) : L.Configuration :=
  fun e => if e = target then g else A e

@[simp] theorem finite_oriented_replaceLink_same
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge)
    (g : L.Gauge) :
    L.replaceLink A target g target = g := by
  simp [FiniteOrientedLatticeWilsonSystem.replaceLink]

@[simp] theorem finite_oriented_replaceLink_of_ne
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target e : L.Edge)
    (g : L.Gauge)
    (h : e ≠ target) :
    L.replaceLink A target g e = A e := by
  simp [FiniteOrientedLatticeWilsonSystem.replaceLink, h]

/-- Replacing a link by its current value leaves the configuration unchanged. -/
theorem finite_oriented_replaceLink_current
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge) :
    L.replaceLink A target (A target) = A := by
  funext e
  by_cases h : e = target
  · subst e
    simp
  · simp [FiniteOrientedLatticeWilsonSystem.replaceLink, h]

/-- Two configurations agree away from one physical source link. -/
def FiniteOrientedLatticeWilsonSystem.AgreeOffLink
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration)
    (source : L.Edge) : Prop :=
  ∀ e : L.Edge, e ≠ source → A e = B e

/-- Signed step values are determined by the value of the underlying physical
link. -/
theorem finite_oriented_stepValue_congr
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration)
    (step : FiniteOrientedBoundaryStep L.Edge)
    (h : A step.edge = B step.edge) :
    L.stepValue A step = L.stepValue B step := by
  cases step with
  | mk edge orientation =>
      cases orientation <;>
        simp [FiniteOrientedLatticeWilsonSystem.stepValue, h]

/-- Signed plaquette holonomy is determined by the four underlying physical
boundary-link values. -/
theorem finite_oriented_plaquetteHolonomy_congr
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration)
    (p : L.Plaquette)
    (hBoundary : ∀ k : Fin 4,
      A (L.boundary p k).edge = B (L.boundary p k).edge) :
    L.plaquetteHolonomy A p = L.plaquetteHolonomy B p := by
  unfold FiniteOrientedLatticeWilsonSystem.plaquetteHolonomy
  rw [finite_oriented_stepValue_congr L A B (L.boundary p 0) (hBoundary 0),
    finite_oriented_stepValue_congr L A B (L.boundary p 1) (hBoundary 1),
    finite_oriented_stepValue_congr L A B (L.boundary p 2) (hBoundary 2),
    finite_oriented_stepValue_congr L A B (L.boundary p 3) (hBoundary 3)]

/-- If `source` shares no plaquette with `target`, changing only `source` does
not alter any physical boundary value of a target-touching plaquette after the
same target replacement. -/
theorem finite_oriented_replaceLink_boundary_eq_of_not_plaquetteNeighbor
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration)
    (target source : L.Edge)
    (g : L.Gauge)
    (p : L.Plaquette)
    (hTarget : L.PlaquetteTouchesEdge p target)
    (hNotNeighbor : source ∉ L.plaquetteNeighbors target)
    (hAgree : L.AgreeOffLink A B source)
    (k : Fin 4) :
    L.replaceLink A target g (L.boundary p k).edge =
      L.replaceLink B target g (L.boundary p k).edge := by
  classical
  have hNotSource : ¬ L.PlaquetteTouchesEdge p source := by
    intro hSource
    apply hNotNeighbor
    exact (finite_oriented_mem_plaquetteNeighbors_iff
      L target source).mpr ⟨p, hTarget, hSource⟩
  by_cases hBoundaryTarget : (L.boundary p k).edge = target
  · simp [FiniteOrientedLatticeWilsonSystem.replaceLink, hBoundaryTarget]
  · have hBoundarySource : (L.boundary p k).edge ≠ source := by
      intro hSource
      exact hNotSource ⟨k, hSource⟩
    simp [FiniteOrientedLatticeWilsonSystem.replaceLink,
      hBoundaryTarget, hAgree (L.boundary p k).edge hBoundarySource]

/-- Holonomy of a target-touching plaquette is insensitive to changing a
non-neighbor source link after a common target replacement. -/
theorem finite_oriented_plaquetteHolonomy_replaceLink_eq_of_not_neighbor
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration)
    (target source : L.Edge)
    (g : L.Gauge)
    (p : L.Plaquette)
    (hTarget : L.PlaquetteTouchesEdge p target)
    (hNotNeighbor : source ∉ L.plaquetteNeighbors target)
    (hAgree : L.AgreeOffLink A B source) :
    L.plaquetteHolonomy (L.replaceLink A target g) p =
      L.plaquetteHolonomy (L.replaceLink B target g) p := by
  apply finite_oriented_plaquetteHolonomy_congr
  intro k
  exact finite_oriented_replaceLink_boundary_eq_of_not_plaquetteNeighbor
    L A B target source g p hTarget hNotNeighbor hAgree k

/-- Corresponding target-plaquette energy is also unchanged. -/
theorem finite_oriented_plaquetteEnergy_replaceLink_eq_of_not_neighbor
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration)
    (target source : L.Edge)
    (g : L.Gauge)
    (p : L.Plaquette)
    (hTarget : L.PlaquetteTouchesEdge p target)
    (hNotNeighbor : source ∉ L.plaquetteNeighbors target)
    (hAgree : L.AgreeOffLink A B source) :
    L.plaquetteEnergy
        (L.plaquetteHolonomy (L.replaceLink A target g) p) =
      L.plaquetteEnergy
        (L.plaquetteHolonomy (L.replaceLink B target g) p) := by
  rw [finite_oriented_plaquetteHolonomy_replaceLink_eq_of_not_neighbor
    L A B target source g p hTarget hNotNeighbor hAgree]

/-- Part of the Wilson action contributed by plaquettes touching `target`. -/
def FiniteOrientedLatticeWilsonSystem.targetLocalPlaquetteAction
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge) : ℝ := by
  classical
  exact ∑ p : L.Plaquette,
    if L.PlaquetteTouchesEdge p target then
      L.plaquetteEnergy (L.plaquetteHolonomy A p)
    else 0

/-- The target-local action is unchanged by modifying a physical source link
outside the target plaquette neighborhood, after a common target replacement. -/
theorem finite_oriented_targetLocalPlaquetteAction_replaceLink_eq_of_not_neighbor
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration)
    (target source : L.Edge)
    (g : L.Gauge)
    (hNotNeighbor : source ∉ L.plaquetteNeighbors target)
    (hAgree : L.AgreeOffLink A B source) :
    L.targetLocalPlaquetteAction (L.replaceLink A target g) target =
      L.targetLocalPlaquetteAction (L.replaceLink B target g) target := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.targetLocalPlaquetteAction
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hTarget : L.PlaquetteTouchesEdge p target
  · simp only [if_pos hTarget]
    exact finite_oriented_plaquetteEnergy_replaceLink_eq_of_not_neighbor
      L A B target source g p hTarget hNotNeighbor hAgree
  · simp [hTarget]

/-- Part of the Wilson action contributed by plaquettes not touching the
selected target link. -/
def FiniteOrientedLatticeWilsonSystem.targetRemotePlaquetteAction
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge) : ℝ := by
  classical
  exact ∑ p : L.Plaquette,
    if L.PlaquetteTouchesEdge p target then 0
    else L.plaquetteEnergy (L.plaquetteHolonomy A p)

/-- The oriented Wilson action splits exactly into target-local and
 target-remote plaquette contributions. -/
theorem finite_oriented_wilsonAction_eq_targetLocal_add_targetRemote
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge) :
    L.wilsonAction A =
      L.targetLocalPlaquetteAction A target +
        L.targetRemotePlaquetteAction A target := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.wilsonAction
    FiniteOrientedLatticeWilsonSystem.targetLocalPlaquetteAction
    FiniteOrientedLatticeWilsonSystem.targetRemotePlaquetteAction
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hTouch : L.PlaquetteTouchesEdge p target
  · simp [hTouch]
  · simp [hTouch]

/-- A plaquette not touching `target` has the same boundary values after any
two replacements of `target`. -/
theorem finite_oriented_replaceLink_boundary_eq_of_not_touches_target
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge)
    (g h : L.Gauge)
    (p : L.Plaquette)
    (hNotTouch : ¬ L.PlaquetteTouchesEdge p target)
    (k : Fin 4) :
    L.replaceLink A target g (L.boundary p k).edge =
      L.replaceLink A target h (L.boundary p k).edge := by
  classical
  have hBoundary : (L.boundary p k).edge ≠ target := by
    intro hk
    exact hNotTouch ⟨k, hk⟩
  simp [FiniteOrientedLatticeWilsonSystem.replaceLink, hBoundary]

/-- Remote plaquette holonomy does not depend on the value inserted at the
selected target link. -/
theorem finite_oriented_plaquetteHolonomy_replaceLink_eq_of_not_touches_target
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge)
    (g h : L.Gauge)
    (p : L.Plaquette)
    (hNotTouch : ¬ L.PlaquetteTouchesEdge p target) :
    L.plaquetteHolonomy (L.replaceLink A target g) p =
      L.plaquetteHolonomy (L.replaceLink A target h) p := by
  apply finite_oriented_plaquetteHolonomy_congr
  intro k
  exact finite_oriented_replaceLink_boundary_eq_of_not_touches_target
    L A target g h p hNotTouch k

/-- Target-remote action is independent of the target replacement value. -/
theorem finite_oriented_targetRemotePlaquetteAction_replaceLink_eq
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge)
    (g h : L.Gauge) :
    L.targetRemotePlaquetteAction (L.replaceLink A target g) target =
      L.targetRemotePlaquetteAction (L.replaceLink A target h) target := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.targetRemotePlaquetteAction
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hTouch : L.PlaquetteTouchesEdge p target
  · simp [hTouch]
  · simp only [if_neg hTouch]
    rw [finite_oriented_plaquetteHolonomy_replaceLink_eq_of_not_touches_target
      L A target g h p hTouch]

/-- Replacing the target by its current value identifies the remote action of
any replacement with that of the original configuration. -/
theorem finite_oriented_targetRemotePlaquetteAction_replaceLink
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge)
    (g : L.Gauge) :
    L.targetRemotePlaquetteAction (L.replaceLink A target g) target =
      L.targetRemotePlaquetteAction A target := by
  calc
    L.targetRemotePlaquetteAction (L.replaceLink A target g) target =
        L.targetRemotePlaquetteAction
          (L.replaceLink A target (A target)) target :=
      finite_oriented_targetRemotePlaquetteAction_replaceLink_eq
        L A target g (A target)
    _ = L.targetRemotePlaquetteAction A target := by
      rw [finite_oriented_replaceLink_current]

/-- The action of a target-updated configuration is its target-local action plus
a target-independent remote constant. -/
theorem finite_oriented_wilsonAction_replaceLink_eq_local_add_remote
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge)
    (g : L.Gauge) :
    L.wilsonAction (L.replaceLink A target g) =
      L.targetLocalPlaquetteAction (L.replaceLink A target g) target +
        L.targetRemotePlaquetteAction A target := by
  rw [finite_oriented_wilsonAction_eq_targetLocal_add_targetRemote,
    finite_oriented_targetRemotePlaquetteAction_replaceLink]

end

end MathlibAnalytic
end MGAP4D
