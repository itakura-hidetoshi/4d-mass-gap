import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialContinuumOSMidpointProductExpectation
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarPathTimeTranslationGeometry
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFixedSlotOSInclusion
import Mathlib.Tactic

/-!
# Factorial continuum OS midpoint identity in one common finite sector

The preceding layer gives the exact product expectation identity

`E[F(x(-(q+t))) G(x(q+t))] = E[F(x(-q)) G(x(q+2t))]`.

This file rewrites that identity in the existing fixed-slot OS bilinear language.  The left-hand
side is the OS form of the time-translated observables on `J+t`.  On the right-hand side the two
observables live naturally on `J` and `J+2t`; both are therefore included into the single finite
common sector

`K = J ∪ (J+2t)`.

This is an exact same-root finite-sector identity.  No closed positive-time algebra, null-space
preservation, quotient descent, contraction estimate, semigroup, Hamiltonian, spectral statement,
or mass-gap transfer is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Common finite slot set containing both the original slots `J` and their `2t` translate. -/
def periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet
    (J : Finset ℚ) (t : ℚ) : Finset ℚ :=
  J ∪
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate
      (t + t) J

/-- The original slots embed canonically into the midpoint common sector. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet_left_subset
    (J : Finset ℚ) (t : ℚ) :
    J ⊆ periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet
      J t := by
  intro q hq
  exact Finset.mem_union_left _ hq

/-- The `2t`-translated slots embed canonically into the midpoint common sector. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet_future_subset
    (J : Finset ℚ) (t : ℚ) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate
        (t + t) J ⊆
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet
        J t := by
  intro q hq
  exact Finset.mem_union_right _ hq

/-- For nonnegative `J` and `t`, the translated OS bilinear form on `J+t` is exactly the mixed
bilinear form obtained by placing `F` on `J` and `T_{2t}G` on `J+2t` inside one common finite slot
sector. -/
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit.factorial_continuum_fixedSlotOSBilinForm_timeTranslate_eq_common_midpoint
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
      L.fixedSlotOSBilinForm H N hN beta hbeta
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet J t)
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion
          J
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet J t)
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet_left_subset
            J t)
          F)
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate
            (t + t) J)
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet J t)
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet_future_subset
            J t)
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
            J (t + t) G)) := by
  rw [L.fixedSlotOSBilinForm_apply, L.fixedSlotOSBilinForm_apply]
  rw [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable_inclusion,
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable_inclusion]
  rw [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation_apply,
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation_apply]
  change
    (∫ x,
        F (fun q : J => x (-(q.1 + t))) *
          G (fun q : J => x (q.1 + t))
      ∂(L.continuumMeasure : Measure (ℚ → ℝ))) =
      ∫ x,
        F (fun q : J => x (-q.1)) *
          G (fun q : J => x (q.1 + (t + t)))
        ∂(L.continuumMeasure : Measure (ℚ → ℝ))
  simpa [add_assoc] using
    L.factorial_continuum_osShiftedPair_product_expectation_eq_midpoint
      H N hN beta hbeta J hJ t ht F G

end

end MathlibAnalytic
end MGAP4D
