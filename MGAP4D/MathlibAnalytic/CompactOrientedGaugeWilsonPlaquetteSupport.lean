import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonAlgebra

/-!
# Plaquette support geometry for compact oriented Wilson systems

This file restores the purely geometric support layer on the current continuous compact
oriented Wilson carrier.  It records which physical positive links are touched by a signed
plaquette boundary, the neighboring links sharing a plaquette, and the corresponding shared
plaquette set.

The layer is independent of the gauge group being finite.  In particular it applies directly
to the actual compact `SU(N)` Wilson systems used by the primary scalar continuum construction.
No Dobrushin contraction, conditional total-variation estimate, clustering rate, covariance
decay, spectral gap, or mass value is asserted here.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A plaquette touches a physical positive link when one of its signed boundary incidences
projects to that link. -/
def CompactOrientedGaugeWilsonSystem.PlaquetteTouchesEdge
    (L : CompactOrientedGaugeWilsonSystem)
    (p : L.geometry.Plaquette)
    (e : L.geometry.Edge) : Prop :=
  ∃ k : Fin 4, (L.geometry.boundary p k).edge = e

/-- Physical positive links sharing at least one plaquette with a target link. -/
noncomputable def CompactOrientedGaugeWilsonSystem.plaquetteNeighbors
    (L : CompactOrientedGaugeWilsonSystem)
    (target : L.geometry.Edge) : Finset L.geometry.Edge := by
  classical
  exact Finset.univ.filter fun source =>
    ∃ p : L.geometry.Plaquette,
      L.PlaquetteTouchesEdge p target ∧ L.PlaquetteTouchesEdge p source

/-- Geometrically active plaquette neighbors, with the diagonal removed. -/
noncomputable def CompactOrientedGaugeWilsonSystem.activePlaquetteNeighbors
    (L : CompactOrientedGaugeWilsonSystem)
    (target : L.geometry.Edge) : Finset L.geometry.Edge := by
  classical
  exact (L.plaquetteNeighbors target).erase target

/-- Plaquettes whose signed boundaries touch both physical links. -/
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

/-- A signed boundary value depends only on the underlying physical link used by that step. -/
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

/-- A plaquette holonomy depends only on the four physical links in its signed boundary. -/
theorem compact_oriented_plaquetteHolonomy_congr
    (L : CompactOrientedGaugeWilsonSystem)
    (A B : L.Configuration)
    (p : L.geometry.Plaquette)
    (hBoundary : ∀ k : Fin 4,
      A (L.geometry.boundary p k).edge =
        B (L.geometry.boundary p k).edge) :
    L.plaquetteHolonomy A p = L.plaquetteHolonomy B p := by
  change
    L.stepValue A (L.geometry.boundary p 0) *
          L.stepValue A (L.geometry.boundary p 1) *
        L.stepValue A (L.geometry.boundary p 2) *
      L.stepValue A (L.geometry.boundary p 3) =
    L.stepValue B (L.geometry.boundary p 0) *
          L.stepValue B (L.geometry.boundary p 1) *
        L.stepValue B (L.geometry.boundary p 2) *
      L.stepValue B (L.geometry.boundary p 3)
  rw [compact_oriented_stepValue_congr L A B _ (hBoundary 0),
    compact_oriented_stepValue_congr L A B _ (hBoundary 1),
    compact_oriented_stepValue_congr L A B _ (hBoundary 2),
    compact_oriented_stepValue_congr L A B _ (hBoundary 3)]

end

end MathlibAnalytic
end MGAP4D
