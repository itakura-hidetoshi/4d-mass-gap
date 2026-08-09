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

/-- Typeclass form of the already-proved canonical Gibbs normalization for the
actual periodic compact `SU(N)` Wilson system.  The specialized head avoids
requiring typeclass search to unfold the model constructor before applying the
generic continuous-compact Wilson probability theorem. -/
instance periodicHypercubicSpecialUnitaryWilsonSystem_gibbsMeasure_probability
    (n N : ℕ)
    [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta) :
    MeasureTheory.IsProbabilityMeasure
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).gibbsMeasure :=
  continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure
    (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta beta_nonneg)

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
