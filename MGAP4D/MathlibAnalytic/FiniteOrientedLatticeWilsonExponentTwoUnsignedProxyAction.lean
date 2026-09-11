import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonDobrushinMatrix
import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonCanonicalRandomScanRayleighSpectralLift

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Unsigned finite-Wilson proxy on the same physical-link and plaquette
carriers.  It is used to transport the Gibbs law and heat-bath Hamiltonian. -/
def FiniteOrientedLatticeWilsonSystem.unsignedProxy
    (L : FiniteOrientedLatticeWilsonSystem) :
    FiniteLatticeWilsonSystem :=
  { Gauge := L.Gauge
    Vertex := Unit
    Edge := L.Edge
    Plaquette := L.Plaquette
    source := fun _ => ()
    target := fun _ => ()
    boundary := fun p k => (L.boundary p k).edge
    boundary_cycle_01 := by intro p; rfl
    boundary_cycle_12 := by intro p; rfl
    boundary_cycle_23 := by intro p; rfl
    boundary_cycle_30 := by intro p; rfl
    plaquetteEnergy := L.plaquetteEnergy
    plaquetteEnergy_nonneg := L.plaquetteEnergy_nonneg
    plaquetteEnergy_conjInvariant := L.plaquetteEnergy_conjInvariant
    beta := L.beta
    beta_nonneg := L.beta_nonneg }

/-- In an exponent-two gauge group, an oriented step contributes the underlying
physical-link value independently of traversal direction. -/
theorem finite_oriented_stepValue_eq_of_inv_eq_self
    (L : FiniteOrientedLatticeWilsonSystem)
    (hInv : ∀ g : L.Gauge, g⁻¹ = g)
    (A : L.Configuration)
    (step : FiniteOrientedBoundaryStep L.Edge) :
    L.stepValue A step = A step.edge := by
  cases step with
  | mk edge orientation =>
      cases orientation
      · rfl
      · simpa [FiniteOrientedLatticeWilsonSystem.stepValue] using
          hInv (A edge)

/-- For exponent-two groups, proxy holonomy equals the orientation-correct
physical-link holonomy. -/
theorem finite_oriented_unsignedProxy_plaquetteHolonomy_eq
    (L : FiniteOrientedLatticeWilsonSystem)
    (hInv : ∀ g : L.Gauge, g⁻¹ = g)
    (A : L.Configuration)
    (p : L.Plaquette) :
    L.unsignedProxy.plaquetteHolonomy A p =
      L.plaquetteHolonomy A p := by
  change
    A (L.boundary p 0).edge *
          A (L.boundary p 1).edge *
        A (L.boundary p 2).edge *
      A (L.boundary p 3).edge =
    L.stepValue A (L.boundary p 0) *
          L.stepValue A (L.boundary p 1) *
        L.stepValue A (L.boundary p 2) *
      L.stepValue A (L.boundary p 3)
  rw [finite_oriented_stepValue_eq_of_inv_eq_self L hInv,
    finite_oriented_stepValue_eq_of_inv_eq_self L hInv,
    finite_oriented_stepValue_eq_of_inv_eq_self L hInv,
    finite_oriented_stepValue_eq_of_inv_eq_self L hInv]

/-- For exponent-two groups, proxy and oriented Wilson actions coincide. -/
theorem finite_oriented_unsignedProxy_wilsonAction_eq
    (L : FiniteOrientedLatticeWilsonSystem)
    (hInv : ∀ g : L.Gauge, g⁻¹ = g)
    (A : L.Configuration) :
    L.unsignedProxy.wilsonAction A = L.wilsonAction A := by
  classical
  unfold FiniteLatticeWilsonSystem.wilsonAction
    FiniteOrientedLatticeWilsonSystem.wilsonAction
  apply Finset.sum_congr rfl
  intro p _hp
  change
    L.plaquetteEnergy (L.unsignedProxy.plaquetteHolonomy A p) =
      L.plaquetteEnergy (L.plaquetteHolonomy A p)
  rw [finite_oriented_unsignedProxy_plaquetteHolonomy_eq L hInv]

end

end MathlibAnalytic
end MGAP4D
