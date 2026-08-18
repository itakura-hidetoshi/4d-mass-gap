import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarPathTimeTranslationGeometry
import Mathlib.Tactic

/-!
# Coherence of rational-time translation for primary scalar finite-slot observables

The preceding layer fixes intrinsic rational-time translation on the same-root scalar path carrier
`ℚ → ℝ` and transports each fixed-slot bounded-continuous observable from a finite slot set `J`
to its translate `J + t`.

This file records the coherence laws needed before any quotient-level OS time evolution is
constructed.  Finite-slot translation preserves zero, addition, and finite union.  Positive-time
translation therefore acts coherently on the canonical finite nonnegative slot indices.  At the
observable level, two successive transports have exactly the same full-path pullback as a single
transport by the summed time, and reflection conjugates the translated pullback by reversing the
path-translation parameter.

All statements are exact identities on the fixed scalar path carrier.  No time-translation
invariance of the continuum measure, OS norm contraction, null-space preservation, semigroup,
Hamiltonian, spectral statement, or mass-gap transfer is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Translating a finite rational slot set by zero leaves it unchanged. -/
@[simp]
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate_zero
    (J : Finset ℚ) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate 0 J = J := by
  ext q
  simp [periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate]

/-- Two successive finite-slot translations add their rational-time parameters. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate_add
    (t s : ℚ) (J : Finset ℚ) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate s
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate t J) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate
        (t + s) J := by
  ext q
  constructor
  · intro hq
    rcases Finset.mem_image.mp hq with ⟨r, hr, rfl⟩
    rcases Finset.mem_image.mp hr with ⟨u, hu, rfl⟩
    exact Finset.mem_image.mpr ⟨u, hu, by ring⟩
  · intro hq
    rcases Finset.mem_image.mp hq with ⟨u, hu, rfl⟩
    refine Finset.mem_image.mpr ⟨u + t, ?_, by ring⟩
    exact Finset.mem_image.mpr ⟨u, hu, rfl⟩

/-- Finite-slot translation commutes with finite union. -/
@[simp]
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate_union
    (t : ℚ) (J K : Finset ℚ) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate t
        (J ∪ K) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate t J ∪
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate t K := by
  simp [periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate,
    Finset.image_union]

/-- Zero positive time acts identically on the canonical finite nonnegative slot index. -/
@[simp]
theorem primaryScalarFiniteNonnegativeSlotIndexTimeTranslate_zero
    (J : PrimaryScalarFiniteNonnegativeSlotIndex) :
    primaryScalarFiniteNonnegativeSlotIndexTimeTranslate 0 le_rfl J = J := by
  apply Subtype.ext
  exact
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate_zero J.1

/-- Successive nonnegative rational translations act additively on canonical finite slot indices. -/
theorem primaryScalarFiniteNonnegativeSlotIndexTimeTranslate_add
    (t s : ℚ) (ht : 0 ≤ t) (hs : 0 ≤ s)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex) :
    primaryScalarFiniteNonnegativeSlotIndexTimeTranslate s hs
        (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate t ht J) =
      primaryScalarFiniteNonnegativeSlotIndexTimeTranslate
        (t + s) (add_nonneg ht hs) J := by
  apply Subtype.ext
  exact
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate_add
      t s J.1

/-- Full-path pullback of a fixed-slot observable after rational-time transport.  This packages the
translated-slot observable and its canonical path pullback as one linear map with a fixed codomain. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservableTimeTranslate
    (J : Finset ℚ) (t : ℚ) :
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservable J →ₗ[ℝ]
      BoundedContinuousFunction (ℚ → ℝ) ℝ :=
  (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate t J)).comp
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
      J t)

/-- The packaged translated pullback is exactly evaluation of the original fixed-slot observable on
the intrinsically translated full path. -/
@[simp]
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservableTimeTranslate_apply
    (J : Finset ℚ) (t : ℚ)
    (F : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservable J)
    (x : ℚ → ℝ) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservableTimeTranslate
        J t F x =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable J F
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathTimeTranslate t x) := by
  exact
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable_timeTranslate
      J t F x

/-- At zero rational time the translated full-path pullback is exactly the original pullback. -/
@[simp]
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservableTimeTranslate_zero
    (J : Finset ℚ) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservableTimeTranslate
        J 0 =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable J := by
  ext F x
  rw [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservableTimeTranslate_apply]
  simp

/-- Two successive fixed-slot observable transports agree exactly on full paths with the single
transport by the summed rational time.  The finite-slot codomains need not be identified by
proof-field equality; coherence is stated on their common canonical full-path pullback. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable_timeTranslate_add
    (J : Finset ℚ) (t s : ℚ)
    (F : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservable J) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate s
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate t J))
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate t J)
          s
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
            J t F)) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate
          (t + s) J)
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
          J (t + s) F) := by
  ext x
  calc
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate s
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate t J))
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate t J)
          s
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
            J t F)) x =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate t J)
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
          J t F)
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathTimeTranslate s x) := by
      rw [
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable_timeTranslate]
    _ = periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable J F
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathTimeTranslate t
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathTimeTranslate s x)) := by
      rw [
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable_timeTranslate]
    _ = periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable J F
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathTimeTranslate (t + s) x) := by
      rw [
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathTimeTranslate_add t s]
    _ = periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate
          (t + s) J)
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
          J (t + s) F) x := by
      symm
      exact
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable_timeTranslate
          J (t + s) F x

/-- Reflection of a translated fixed-slot pullback is exactly the original pullback evaluated on the
reflected path translated by the opposite parameter.  This is the algebraic OS conjugacy identity
needed before any measure-level stationarity argument. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable_timeTranslate_reflection
    (J : Finset ℚ) (t : ℚ)
    (F : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservable J)
    (x : ℚ → ℝ) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate t J)
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
          J t F)
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection x) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable J F
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathTimeTranslate (-t) x)) := by
  rw [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable_timeTranslate]
  congr 1
  symm
  simpa using
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection_timeTranslate
      (-t) x)

end

end MathlibAnalytic
end MGAP4D
