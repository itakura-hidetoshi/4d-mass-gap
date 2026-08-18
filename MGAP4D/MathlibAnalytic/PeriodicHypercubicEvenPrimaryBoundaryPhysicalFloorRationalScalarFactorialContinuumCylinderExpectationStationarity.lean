import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialContinuumFiniteLawStationarity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarPathTimeTranslationGeometry
import Mathlib.Tactic

/-!
# Factorial continuum cylinder expectation stationarity

The preceding layer identifies the shifted and unshifted finite-dimensional probability laws of the
same-root primary scalar continuum process.  This file converts that measure-level statement into
the expectation identity needed by the OS Hilbert carrier.

For a bounded-continuous observable `F` on a fixed finite nonnegative rational slot set `J`, the
expectation of `F` evaluated at `q+t` equals its expectation at `q`.  The existing intrinsic
rational-time geometry then rewrites this as exact expectation preservation for the canonical
transport `FixedSlotObservableTimeTranslate` from `J` to `J+t`.

No whole-path translation invariance, OS contraction, null-space preservation, semigroup,
Hamiltonian, spectral statement, or mass-gap transfer is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Finite-dimensional continuum stationarity implies equality of expectations of every
bounded-continuous test observable on the fixed scalar coordinate space `J → ℝ`. -/
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit.factorial_continuum_finiteRestriction_expectation_stationary
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
    (F : BoundedContinuousFunction (∀ q : J, ℝ) ℝ) :
    (∫ x,
        F
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarShiftedFiniteRestrictionContinuousMap
            J t x)
      ∂(L.continuumMeasure : Measure (ℚ → ℝ))) =
      ∫ x,
        F
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteRestrictionContinuousMap
            J x)
        ∂(L.continuumMeasure : Measure (ℚ → ℝ)) := by
  let τ : C(ℚ → ℝ, ∀ q : J, ℝ) :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarShiftedFiniteRestrictionContinuousMap
      J t
  let ρ : C(ℚ → ℝ, ∀ q : J, ℝ) :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteRestrictionContinuousMap J
  have hPM :=
    L.factorial_continuum_finiteRestriction_law_stationary
      H N hN beta hbeta J hJ t ht
  have hLaw :
      Measure.map τ (L.continuumMeasure : Measure (ℚ → ℝ)) =
        Measure.map ρ (L.continuumMeasure : Measure (ℚ → ℝ)) := by
    simpa [τ, ρ] using congrArg ProbabilityMeasure.toMeasure hPM
  calc
    (∫ x, F (τ x) ∂(L.continuumMeasure : Measure (ℚ → ℝ))) =
        ∫ v, F v ∂Measure.map τ (L.continuumMeasure : Measure (ℚ → ℝ)) := by
      symm
      exact
        MeasureTheory.integral_map
          τ.measurable.aemeasurable F.continuous.aestronglyMeasurable
    _ = ∫ v, F v ∂Measure.map ρ (L.continuumMeasure : Measure (ℚ → ℝ)) := by
      rw [hLaw]
    _ = ∫ x, F (ρ x) ∂(L.continuumMeasure : Measure (ℚ → ℝ)) := by
      exact
        MeasureTheory.integral_map
          ρ.measurable.aemeasurable F.continuous.aestronglyMeasurable

/-- The canonical transport of a fixed-slot bounded-continuous observable to the translated slot
set preserves its ordinary continuum expectation exactly. -/
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit.factorial_continuum_fixedSlotObservableTimeTranslate_expectation_eq
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
    (F : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservable J) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation
        L.continuumMeasure
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate t J)
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
            J t F)) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation
        L.continuumMeasure
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable
          J F) := by
  rw [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation_apply,
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation_apply]
  have h :=
    L.factorial_continuum_finiteRestriction_expectation_stationary
      H N hN beta hbeta J hJ t ht F
  simpa only [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable_timeTranslate,
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable_apply,
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarShiftedFiniteRestrictionContinuousMap_apply]
    using h

end

end MathlibAnalytic
end MGAP4D
