import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonContinuousSystem

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Finite oriented four-step plaquette geometry, separated from the gauge group
and the Wilson energy. -/
structure FiniteFourDimensionalPlaquetteGeometry where
  Vertex : Type
  [vertexFintype : Fintype Vertex]
  Edge : Type
  [edgeFintype : Fintype Edge]
  Plaquette : Type
  [plaquetteFintype : Fintype Plaquette]
  source : Edge → Vertex
  target : Edge → Vertex
  boundary : Plaquette → Fin 4 → Edge
  boundary_cycle_01 :
    ∀ p, target (boundary p 0) = source (boundary p 1)
  boundary_cycle_12 :
    ∀ p, target (boundary p 1) = source (boundary p 2)
  boundary_cycle_23 :
    ∀ p, target (boundary p 2) = source (boundary p 3)
  boundary_cycle_30 :
    ∀ p, target (boundary p 3) = source (boundary p 0)

attribute [instance]
  FiniteFourDimensionalPlaquetteGeometry.vertexFintype
  FiniteFourDimensionalPlaquetteGeometry.edgeFintype
  FiniteFourDimensionalPlaquetteGeometry.plaquetteFintype

end

end MathlibAnalytic
end MGAP4D
