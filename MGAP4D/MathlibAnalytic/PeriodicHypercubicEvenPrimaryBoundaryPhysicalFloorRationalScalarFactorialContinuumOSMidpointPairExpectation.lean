import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialContinuumOSMidpointPairLaw
import Mathlib.Tactic

/-!
# Factorial continuum OS midpoint pair expectation identity

The preceding layer identifies, under the same canonical primary-scalar continuum law, the fixed
finite-dimensional law of the translated symmetric OS pair

`(q ↦ x (-(q+t)), q ↦ x (q+t))`

with the midpoint pair

`(q ↦ x (-q), q ↦ x ((q+t)+t))`.

This file converts that probability-law identity into the corresponding expectation identity for
an arbitrary bounded-continuous test function on the fixed pair carrier
`(J → ℝ) × (J → ℝ)`.  This is the direct pair analogue of the already-canonical continuum cylinder
expectation stationarity layer.

No OS contraction, null-space preservation, quotient descent, semigroup, Hamiltonian, spectral
statement, or mass-gap transfer is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The factorial continuum OS midpoint pair-law identity preserves the expectation of every
bounded-continuous test function on the fixed pair carrier. -/
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit.factorial_continuum_osShiftedPair_expectation_eq_midpoint
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
    (Phi : BoundedContinuousFunction
      ((∀ q : J, ℝ) × (∀ q : J, ℝ)) ℝ) :
    (∫ x,
        Phi
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSShiftedPairContinuousMap
            J t x)
      ∂(L.continuumMeasure : Measure (ℚ → ℝ))) =
      ∫ x,
        Phi
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointPairContinuousMap
            J t x)
        ∂(L.continuumMeasure : Measure (ℚ → ℝ)) := by
  let P : C(ℚ → ℝ, (∀ q : J, ℝ) × (∀ q : J, ℝ)) :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSShiftedPairContinuousMap
      J t
  let Q : C(ℚ → ℝ, (∀ q : J, ℝ) × (∀ q : J, ℝ)) :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointPairContinuousMap
      J t
  have hPM :=
    L.factorial_continuum_osShiftedPair_law_eq_midpoint
      H N hN beta hbeta J hJ t ht
  have hLaw :
      Measure.map P (L.continuumMeasure : Measure (ℚ → ℝ)) =
        Measure.map Q (L.continuumMeasure : Measure (ℚ → ℝ)) := by
    simpa [P, Q] using congrArg ProbabilityMeasure.toMeasure hPM
  calc
    (∫ x, Phi (P x) ∂(L.continuumMeasure : Measure (ℚ → ℝ))) =
        ∫ v, Phi v ∂Measure.map P (L.continuumMeasure : Measure (ℚ → ℝ)) := by
      symm
      exact
        MeasureTheory.integral_map
          P.measurable.aemeasurable Phi.continuous.aestronglyMeasurable
    _ = ∫ v, Phi v ∂Measure.map Q (L.continuumMeasure : Measure (ℚ → ℝ)) := by
      rw [hLaw]
    _ = ∫ x, Phi (Q x) ∂(L.continuumMeasure : Measure (ℚ → ℝ)) := by
      exact
        MeasureTheory.integral_map
          Q.measurable.aemeasurable Phi.continuous.aestronglyMeasurable

end

end MathlibAnalytic
end MGAP4D
