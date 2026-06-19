import MGAP4D.MathlibAnalytic.PeriodicHypercubicFiniteOrientedGeometry
import MGAP4D.MathlibAnalytic.SpecialUnitaryCompactOrientedGaugeWilsonSystem

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Canonical finite-volume `SU(N)` Wilson system on the signed periodic
four-dimensional lattice. -/
def periodicHypercubicSpecialUnitaryWilsonSystem
    (n N : ℕ)
    [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta) :
    ContinuousCompactOrientedGaugeWilsonSystem :=
  specialUnitaryContinuousCompactOrientedGaugeWilsonSystem
    (periodicHypercubicFiniteOrientedGeometry n)
    N hN beta beta_nonneg

/-- The plaquette holonomy of the canonical compact system is exactly the
previously constructed signed periodic holonomy. -/
theorem periodicHypercubicSpecialUnitaryWilsonSystem_plaquetteHolonomy
    (n N : ℕ)
    [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (A : PeriodicHypercubicEdge n →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (p : PeriodicHypercubicPlaquette n) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).base.plaquetteHolonomy A p =
      periodicHypercubicPlaquetteHolonomy A p := by
  rfl

/-- The finite-volume action is the sum of the canonical `SU(N)` Wilson energy
of the signed periodic plaquette holonomies. -/
theorem periodicHypercubicSpecialUnitaryWilsonSystem_wilsonAction
    (n N : ℕ)
    [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (A : PeriodicHypercubicEdge n →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).base.wilsonAction A =
      ∑ p : PeriodicHypercubicPlaquette n,
        specialUnitaryWilsonPlaquetteEnergy N
          (periodicHypercubicPlaquetteHolonomy A p) := by
  rfl

end

end MathlibAnalytic
end MGAP4D
