import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialContinuumOSMidpointPairExpectation
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarPathContinuumOSBilinearForm
import Mathlib.Tactic

/-!
# Factorial continuum OS midpoint product expectation

The preceding layer proves the continuum midpoint expectation identity for every bounded-continuous
test function on the fixed pair carrier

`(J → ℝ) × (J → ℝ)`.

Here we specialize that theorem to the product test

`(u,v) ↦ F(u) * G(v)`

for arbitrary bounded-continuous fixed-slot observables `F` and `G`.  This gives exactly the
bilinear integrand identity needed to rewrite translated OS forms in a common finite-slot sector.
Keeping `F` and `G` independent avoids rebuilding a quadratic-only theorem before the existing
bilinear OS API is used.

No OS contraction, null-space preservation, quotient descent, semigroup, Hamiltonian, spectral
statement, or mass-gap transfer is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The translated symmetric OS product expectation equals its midpoint-resolved product
expectation for arbitrary fixed-slot bounded-continuous observables `F` and `G`. -/
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit.factorial_continuum_osShiftedPair_product_expectation_eq_midpoint
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
    (∫ x,
        F (fun q : J => x (-(q.1 + t))) *
          G (fun q : J => x (q.1 + t))
      ∂(L.continuumMeasure : Measure (ℚ → ℝ))) =
      ∫ x,
        F (fun q : J => x (-q.1)) *
          G (fun q : J => x ((q.1 + t) + t))
        ∂(L.continuumMeasure : Measure (ℚ → ℝ)) := by
  let fstMap :
      C(((∀ q : J, ℝ) × (∀ q : J, ℝ)), ∀ q : J, ℝ) :=
    ⟨Prod.fst, continuous_fst⟩
  let sndMap :
      C(((∀ q : J, ℝ) × (∀ q : J, ℝ)), ∀ q : J, ℝ) :=
    ⟨Prod.snd, continuous_snd⟩
  let Phi : BoundedContinuousFunction
      ((∀ q : J, ℝ) × (∀ q : J, ℝ)) ℝ :=
    (F.compContinuous fstMap) * (G.compContinuous sndMap)
  have h :=
    L.factorial_continuum_osShiftedPair_expectation_eq_midpoint
      H N hN beta hbeta J hJ t ht Phi
  simpa [Phi, fstMap, sndMap] using h

end

end MathlibAnalytic
end MGAP4D
