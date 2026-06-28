import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonSingleLinkConditional

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A compact oriented plaquette touches a physical positive link when one
signed boundary incidence projects to that link. -/
def CompactOrientedGaugeWilsonSystem.PlaquetteTouchesEdge
    (L : CompactOrientedGaugeWilsonSystem)
    (p : L.geometry.Plaquette)
    (e : L.geometry.Edge) : Prop :=
  ∃ k : Fin 4, (L.geometry.boundary p k).edge = e

/-- Physical links sharing at least one plaquette with a target link. -/
noncomputable def CompactOrientedGaugeWilsonSystem.plaquetteNeighbors
    (L : CompactOrientedGaugeWilsonSystem)
    (target : L.geometry.Edge) : Finset L.geometry.Edge := by
  classical
  exact Finset.univ.filter fun source =>
    ∃ p : L.geometry.Plaquette,
      L.PlaquetteTouchesEdge p target ∧ L.PlaquetteTouchesEdge p source

/-- Geometrically active compact physical links, with the diagonal removed. -/
noncomputable def CompactOrientedGaugeWilsonSystem.activePlaquetteNeighbors
    (L : CompactOrientedGaugeWilsonSystem)
    (target : L.geometry.Edge) : Finset L.geometry.Edge := by
  classical
  exact (L.plaquetteNeighbors target).erase target

/-- Compact oriented plaquettes touching both physical links. -/
noncomputable def CompactOrientedGaugeWilsonSystem.sharedPlaquettes
    (L : CompactOrientedGaugeWilsonSystem)
    (target source : L.geometry.Edge) : Finset L.geometry.Plaquette := by
  classical
  exact Finset.univ.filter fun p =>
    L.PlaquetteTouchesEdge p target ∧ L.PlaquetteTouchesEdge p source

@[simp] theorem compact_oriented_mem_plaquetteNeighbors_iff
    (L : CompactOrientedGaugeWilsonSystem)
    (target source : L.geometry.Edge) :
    source ∈ L.plaquetteNeighbors target ↔
      ∃ p : L.geometry.Plaquette,
        L.PlaquetteTouchesEdge p target ∧ L.PlaquetteTouchesEdge p source := by
  classical
  simp [CompactOrientedGaugeWilsonSystem.plaquetteNeighbors]

@[simp] theorem compact_oriented_mem_activePlaquetteNeighbors_iff
    (L : CompactOrientedGaugeWilsonSystem)
    (target source : L.geometry.Edge) :
    source ∈ L.activePlaquetteNeighbors target ↔
      (∃ p : L.geometry.Plaquette,
        L.PlaquetteTouchesEdge p target ∧ L.PlaquetteTouchesEdge p source) ∧
        source ≠ target := by
  classical
  simp [CompactOrientedGaugeWilsonSystem.activePlaquetteNeighbors,
    compact_oriented_mem_plaquetteNeighbors_iff, and_comm]

@[simp] theorem compact_oriented_mem_sharedPlaquettes_iff
    (L : CompactOrientedGaugeWilsonSystem)
    (target source : L.geometry.Edge)
    (p : L.geometry.Plaquette) :
    p ∈ L.sharedPlaquettes target source ↔
      L.PlaquetteTouchesEdge p target ∧ L.PlaquetteTouchesEdge p source := by
  classical
  simp [CompactOrientedGaugeWilsonSystem.sharedPlaquettes]

/-- Compact signed step values depend only on the underlying physical-link
value. -/
theorem compact_oriented_stepValue_congr
    (L : CompactOrientedGaugeWilsonSystem)
    (A B : L.Configuration)
    (step : FiniteOrientedBoundaryStep L.geometry.Edge)
    (h : A step.edge = B step.edge) :
    L.stepValue A step = L.stepValue B step := by
  cases step with
  | mk edge orientation =>
      cases orientation <;>
        simp [CompactOrientedGaugeWilsonSystem.stepValue,
          FiniteOrientedFourDimensionalPlaquetteGeometry.stepValue, h]

/-- Compact signed plaquette holonomy is determined by its four physical
boundary-link values. -/
theorem compact_oriented_plaquetteHolonomy_congr
    (L : CompactOrientedGaugeWilsonSystem)
    (A B : L.Configuration)
    (p : L.geometry.Plaquette)
    (hBoundary : ∀ k : Fin 4,
      A (L.geometry.boundary p k).edge =
        B (L.geometry.boundary p k).edge) :
    L.plaquetteHolonomy A p = L.plaquetteHolonomy B p := by
  unfold CompactOrientedGaugeWilsonSystem.plaquetteHolonomy
    FiniteOrientedFourDimensionalPlaquetteGeometry.plaquetteHolonomy
  rw [compact_oriented_stepValue_congr L A B _ (hBoundary 0),
    compact_oriented_stepValue_congr L A B _ (hBoundary 1),
    compact_oriented_stepValue_congr L A B _ (hBoundary 2),
    compact_oriented_stepValue_congr L A B _ (hBoundary 3)]

end
end MathlibAnalytic
end MGAP4D
