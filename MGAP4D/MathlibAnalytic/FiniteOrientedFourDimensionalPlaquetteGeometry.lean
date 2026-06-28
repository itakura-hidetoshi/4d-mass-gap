import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonSystem

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Finite four-step plaquette geometry whose configurations remain attached to
physical positive links while boundary incidences remember traversal direction. -/
structure FiniteOrientedFourDimensionalPlaquetteGeometry where
  Vertex : Type
  [vertexFintype : Fintype Vertex]
  Edge : Type
  [edgeFintype : Fintype Edge]
  Plaquette : Type
  [plaquetteFintype : Fintype Plaquette]
  edgeSource : Edge → Vertex
  edgeTarget : Edge → Vertex
  boundary : Plaquette → Fin 4 → FiniteOrientedBoundaryStep Edge
  boundary_cycle_01 : ∀ p,
    (boundary p 0).terminal edgeSource edgeTarget =
      (boundary p 1).initial edgeSource edgeTarget
  boundary_cycle_12 : ∀ p,
    (boundary p 1).terminal edgeSource edgeTarget =
      (boundary p 2).initial edgeSource edgeTarget
  boundary_cycle_23 : ∀ p,
    (boundary p 2).terminal edgeSource edgeTarget =
      (boundary p 3).initial edgeSource edgeTarget
  boundary_cycle_30 : ∀ p,
    (boundary p 3).terminal edgeSource edgeTarget =
      (boundary p 0).initial edgeSource edgeTarget

attribute [instance]
  FiniteOrientedFourDimensionalPlaquetteGeometry.vertexFintype
  FiniteOrientedFourDimensionalPlaquetteGeometry.edgeFintype
  FiniteOrientedFourDimensionalPlaquetteGeometry.plaquetteFintype

/-- Value of one signed boundary incidence for a physical-link field. -/
def FiniteOrientedFourDimensionalPlaquetteGeometry.stepValue
    (G : FiniteOrientedFourDimensionalPlaquetteGeometry)
    {Gauge : Type} [Group Gauge]
    (A : G.Edge → Gauge)
    (step : FiniteOrientedBoundaryStep G.Edge) : Gauge :=
  match step.orientation with
  | .forward => A step.edge
  | .backward => (A step.edge)⁻¹

/-- Ordered holonomy of a signed four-step boundary. -/
def FiniteOrientedFourDimensionalPlaquetteGeometry.plaquetteHolonomy
    (G : FiniteOrientedFourDimensionalPlaquetteGeometry)
    {Gauge : Type} [Group Gauge]
    (A : G.Edge → Gauge)
    (p : G.Plaquette) : Gauge :=
  G.stepValue A (G.boundary p 0) *
    G.stepValue A (G.boundary p 1) *
    G.stepValue A (G.boundary p 2) *
    G.stepValue A (G.boundary p 3)

end

end MathlibAnalytic
end MGAP4D
