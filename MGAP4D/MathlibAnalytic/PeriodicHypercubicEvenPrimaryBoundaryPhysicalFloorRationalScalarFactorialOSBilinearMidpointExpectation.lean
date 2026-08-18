import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialContinuumOSMidpointProductExpectation
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarPathTimeTranslationGeometry
import Mathlib.Tactic

/-!
# Factorial translated OS bilinear form as a midpoint expectation

The preceding same-root continuum layer proves the product midpoint identity for arbitrary
fixed-slot observables `F` and `G`.  This file rewrites its translated left-hand side in the
canonical fixed-slot Osterwalder--Schrader bilinear form.

For a finite nonnegative rational slot set `J` and `t ≥ 0`, the canonical observable transport sends
`F,G` to the translated slot set `J+t`.  The OS form there is exactly

`E[F(x(-(q+t))) G(x(q+t))]`.

Consequently the product midpoint theorem becomes

`B_{J+t}(T_t F, T_t G) = E[F(x(-q)) G(x(q+2t))]`.

The right-hand side is deliberately left as an explicit same-root path expectation here.  The next
layer will place `J` and `J+2t` into their canonical finite union sector.  No quotient descent,
null-space preservation, OS contraction, semigroup, Hamiltonian, spectral statement, or mass-gap
transfer is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The OS bilinear form of two equally time-translated fixed-slot observables is the explicit
midpoint-resolved continuum product expectation. -/
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit.factorial_fixedSlotOSBilinForm_timeTranslate_eq_midpointExpectation
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (L :
      PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
        H N hN beta hbeta
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing)
    (J : Finset ℚ)
    (hJ : ∀ q : J, (0 : ℚ) ≤ q.1)
    (t : ℚ) (ht : 0 ≤ t)
    (F G : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservable J) :
    L.fixedSlotOSBilinForm H N hN beta hbeta
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate t J)
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
          J t F)
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
          J t G) =
      ∫ x,
        F (fun q : J => x (-q.1)) *
          G (fun q : J => x ((q.1 + t) + t))
        ∂(L.continuumMeasure : Measure (ℚ → ℝ)) := by
  have h :=
    L.factorial_continuum_osShiftedPair_product_expectation_eq_midpoint
      H N hN beta hbeta J hJ t ht F G
  rw [L.fixedSlotOSBilinForm_apply]
  rw [periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation_apply]
  change
    (∫ x,
        F (fun q : J => x (-(q.1 + t))) *
          G (fun q : J => x (q.1 + t))
      ∂(L.continuumMeasure : Measure (ℚ → ℝ))) =
      ∫ x,
        F (fun q : J => x (-q.1)) *
          G (fun q : J => x ((q.1 + t) + t))
        ∂(L.continuumMeasure : Measure (ℚ → ℝ))
  exact h

end

end MathlibAnalytic
end MGAP4D
