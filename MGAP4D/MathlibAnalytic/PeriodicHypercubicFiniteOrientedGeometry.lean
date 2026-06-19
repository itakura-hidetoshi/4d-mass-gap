import MGAP4D.MathlibAnalytic.PeriodicHypercubicGeometryBridge

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

def periodicHypercubicFiniteOrientedGeometry
    (n : ℕ) [NeZero n] :
    FiniteOrientedFourDimensionalPlaquetteGeometry where
  Vertex := PeriodicHypercubicVertex n
  Edge := PeriodicHypercubicEdge n
  Plaquette := PeriodicHypercubicPlaquette n
  edgeSource := periodicHypercubicEdgeSource n
  edgeTarget := periodicHypercubicEdgeTarget n
  boundary := fun p k =>
    periodicBoundaryStepToFinite (periodicHypercubicBoundaryStep n p k)
  boundary_cycle_01 := by
    intro p
    simpa using periodicHypercubic_boundary_cycle_01 n p
  boundary_cycle_12 := by
    intro p
    simpa using periodicHypercubic_boundary_cycle_12 n p
  boundary_cycle_23 := by
    intro p
    simpa using periodicHypercubic_boundary_cycle_23 n p
  boundary_cycle_30 := by
    intro p
    simpa using periodicHypercubic_boundary_cycle_30 n p

@[simp]
theorem periodicHypercubicFiniteOrientedGeometry_stepValue
    {n : ℕ} [NeZero n]
    {Gauge : Type} [Group Gauge]
    (A : PeriodicHypercubicEdge n → Gauge)
    (s : PeriodicHypercubicBoundaryStep n) :
    (periodicHypercubicFiniteOrientedGeometry n).stepValue A
        (periodicBoundaryStepToFinite s) =
      periodicHypercubicStepValue A s := by
  cases s with
  | mk edge orientation => cases orientation <;> rfl

/-- The generic oriented holonomy agrees exactly with the signed periodic
plaquette holonomy. -/
theorem periodicHypercubicFiniteOrientedGeometry_plaquetteHolonomy
    {n : ℕ} [NeZero n]
    {Gauge : Type} [Group Gauge]
    (A : PeriodicHypercubicEdge n → Gauge)
    (p : PeriodicHypercubicPlaquette n) :
    (periodicHypercubicFiniteOrientedGeometry n).plaquetteHolonomy A p =
      periodicHypercubicPlaquetteHolonomy A p := by
  rfl

end

end MathlibAnalytic
end MGAP4D
