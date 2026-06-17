import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonCanonicalDobrushinLocalMajorant

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A plaquette touches an edge when that edge occurs in its ordered boundary. -/
def FiniteLatticeWilsonSystem.PlaquetteTouchesEdge
    (L : FiniteLatticeWilsonSystem)
    (p : L.Plaquette) (e : L.Edge) : Prop :=
  ∃ k : Fin 4, L.boundary p k = e

/-- The finite set of source links sharing at least one plaquette with a target
link.  This is the geometric candidate support of the target conditional law. -/
noncomputable def FiniteLatticeWilsonSystem.plaquetteNeighbors
    (L : FiniteLatticeWilsonSystem)
    (target : L.Edge) : Finset L.Edge := by
  classical
  exact Finset.univ.filter fun source =>
    ∃ p : L.Plaquette,
      L.PlaquetteTouchesEdge p target ∧
        L.PlaquetteTouchesEdge p source

@[simp] theorem finite_lattice_mem_plaquetteNeighbors_iff
    (L : FiniteLatticeWilsonSystem)
    (target source : L.Edge) :
    source ∈ L.plaquetteNeighbors target ↔
      ∃ p : L.Plaquette,
        L.PlaquetteTouchesEdge p target ∧
          L.PlaquetteTouchesEdge p source := by
  classical
  simp [FiniteLatticeWilsonSystem.plaquetteNeighbors]

/-- The plaquette-neighbor set is bounded by the total finite edge count. -/
theorem finite_lattice_plaquetteNeighbors_card_le_edgeCard
    (L : FiniteLatticeWilsonSystem)
    (target : L.Edge) :
    (L.plaquetteNeighbors target).card ≤ Fintype.card L.Edge := by
  classical
  simpa using Finset.card_le_card (Finset.subset_univ (L.plaquetteNeighbors target))

/-- Plaquette holonomy is determined pointwise by the four boundary-link values. -/
theorem finite_lattice_plaquetteHolonomy_congr
    (L : FiniteLatticeWilsonSystem)
    (A B : L.Configuration)
    (p : L.Plaquette)
    (hBoundary : ∀ k : Fin 4,
      A (L.boundary p k) = B (L.boundary p k)) :
    L.plaquetteHolonomy A p = L.plaquetteHolonomy B p := by
  unfold FiniteLatticeWilsonSystem.plaquetteHolonomy
  rw [hBoundary 0, hBoundary 1, hBoundary 2, hBoundary 3]

/-- If `source` shares no plaquette with `target`, then changing only `source`
does not alter any boundary value of a target-touching plaquette after the same
target replacement. -/
theorem finite_lattice_replaceLink_boundary_eq_of_not_plaquetteNeighbor
    (L : FiniteLatticeWilsonSystem)
    (A B : L.Configuration)
    (target source : L.Edge)
    (g : L.Gauge)
    (p : L.Plaquette)
    (hTarget : L.PlaquetteTouchesEdge p target)
    (hNotNeighbor : source ∉ L.plaquetteNeighbors target)
    (hAgree : L.AgreeOffLink A B source)
    (k : Fin 4) :
    L.replaceLink A target g (L.boundary p k) =
      L.replaceLink B target g (L.boundary p k) := by
  classical
  have hNotSource : ¬ L.PlaquetteTouchesEdge p source := by
    intro hSource
    apply hNotNeighbor
    exact finite_lattice_mem_plaquetteNeighbors_iff L target source |>.2
      ⟨p, hTarget, hSource⟩
  by_cases hBoundaryTarget : L.boundary p k = target
  · simp [hBoundaryTarget]
  · have hBoundarySource : L.boundary p k ≠ source := by
      intro hSource
      exact hNotSource ⟨k, hSource⟩
    simp [FiniteLatticeWilsonSystem.replaceLink,
      hBoundaryTarget, hAgree (L.boundary p k) hBoundarySource]

/-- Target-plaquette holonomy is insensitive to changing a non-neighbor source
link, once the target is replaced by the same gauge value. -/
theorem finite_lattice_plaquetteHolonomy_replaceLink_eq_of_not_neighbor
    (L : FiniteLatticeWilsonSystem)
    (A B : L.Configuration)
    (target source : L.Edge)
    (g : L.Gauge)
    (p : L.Plaquette)
    (hTarget : L.PlaquetteTouchesEdge p target)
    (hNotNeighbor : source ∉ L.plaquetteNeighbors target)
    (hAgree : L.AgreeOffLink A B source) :
    L.plaquetteHolonomy (L.replaceLink A target g) p =
      L.plaquetteHolonomy (L.replaceLink B target g) p := by
  apply finite_lattice_plaquetteHolonomy_congr
  intro k
  exact finite_lattice_replaceLink_boundary_eq_of_not_plaquetteNeighbor
    L A B target source g p hTarget hNotNeighbor hAgree k

/-- The corresponding target-plaquette energy is also unchanged. -/
theorem finite_lattice_plaquetteEnergy_replaceLink_eq_of_not_neighbor
    (L : FiniteLatticeWilsonSystem)
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
  rw [finite_lattice_plaquetteHolonomy_replaceLink_eq_of_not_neighbor
    L A B target source g p hTarget hNotNeighbor hAgree]

/-- The part of the Wilson action contributed by plaquettes touching `target`. -/
def FiniteLatticeWilsonSystem.targetLocalPlaquetteAction
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge) : ℝ := by
  classical
  exact ∑ p ∈ Finset.univ,
    if L.PlaquetteTouchesEdge p target then
      L.plaquetteEnergy (L.plaquetteHolonomy A p)
    else 0

/-- The target-local plaquette action is unchanged by modifying a source link
outside the target plaquette neighborhood, after a common target replacement. -/
theorem finite_lattice_targetLocalPlaquetteAction_replaceLink_eq_of_not_neighbor
    (L : FiniteLatticeWilsonSystem)
    (A B : L.Configuration)
    (target source : L.Edge)
    (g : L.Gauge)
    (hNotNeighbor : source ∉ L.plaquetteNeighbors target)
    (hAgree : L.AgreeOffLink A B source) :
    L.targetLocalPlaquetteAction (L.replaceLink A target g) target =
      L.targetLocalPlaquetteAction (L.replaceLink B target g) target := by
  classical
  unfold FiniteLatticeWilsonSystem.targetLocalPlaquetteAction
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hTarget : L.PlaquetteTouchesEdge p target
  · simp only [if_pos hTarget]
    exact finite_lattice_plaquetteEnergy_replaceLink_eq_of_not_neighbor
      L A B target source g p hTarget hNotNeighbor hAgree
  · simp [hTarget]

end

end MathlibAnalytic
end MGAP4D
