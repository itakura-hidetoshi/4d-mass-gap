import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarHilbertCompletion
import Mathlib.Tactic

/-!
# Rational-time translation geometry for the primary scalar OS path

The same-root primary scalar continuum law and its all-finite-slot OS Hilbert completion live on the
fixed path carrier `ℚ → ℝ`.  Before constructing any OS time-translation operator, this file fixes
the intrinsic rational-time geometry on that carrier.

For `t : ℚ`, path translation is the coordinate shift

`(τ_t x)(q) = x(q + t)`.

We prove continuity, the additive action law, and conjugacy with intrinsic time reflection.  For
`t ≥ 0`, translation also sends every finite nonnegative rational slot set to another finite
nonnegative rational slot set.  Finally, fixed-slot bounded-continuous observables are transported
canonically to the translated slot set, and their full-path pullbacks agree exactly with path
translation.

No translation invariance of the continuum measure, OS contraction, semigroup, Hamiltonian,
spectral statement, or mass-gap transfer is asserted here.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Intrinsic rational Euclidean-time translation on the fixed scalar path carrier. -/
def periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathTimeTranslate
    (t : ℚ) (x : ℚ → ℝ) : ℚ → ℝ :=
  fun q => x (q + t)

@[simp]
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathTimeTranslate_apply
    (t q : ℚ) (x : ℚ → ℝ) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathTimeTranslate t x q =
      x (q + t) :=
  rfl

/-- Zero rational time acts identically on scalar paths. -/
@[simp]
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathTimeTranslate_zero
    (x : ℚ → ℝ) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathTimeTranslate 0 x = x := by
  funext q
  simp [periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathTimeTranslate]

/-- Successive intrinsic rational-time translations add their parameters. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathTimeTranslate_add
    (s t : ℚ) (x : ℚ → ℝ) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathTimeTranslate s
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathTimeTranslate t x) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathTimeTranslate (s + t) x := by
  funext q
  simp [periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathTimeTranslate, add_assoc]

/-- Intrinsic path reflection conjugates time translation by reversing its parameter. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection_timeTranslate
    (t : ℚ) (x : ℚ → ℝ) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathTimeTranslate t x) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathTimeTranslate (-t)
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection x) := by
  funext q
  change x (-q + t) = x (-(q + -t))
  congr 1
  ring

/-- Every intrinsic rational-time translation is continuous in the product topology. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathTimeTranslate_continuous
    (t : ℚ) :
    Continuous
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathTimeTranslate t) := by
  apply continuous_pi
  intro q
  exact continuous_apply (q + t)

/-- Intrinsic rational-time translation as a continuous map. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathTimeTranslateContinuousMap
    (t : ℚ) : C(ℚ → ℝ, ℚ → ℝ) :=
  ⟨periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathTimeTranslate t,
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathTimeTranslate_continuous t⟩

/-- Translate a finite rational slot set by `t`. -/
def periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate
    (t : ℚ) (J : Finset ℚ) : Finset ℚ :=
  J.image (fun q => q + t)

/-- A nonnegative slot set remains nonnegative after translation by a nonnegative rational time. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate_nonneg
    (t : ℚ) (ht : 0 ≤ t)
    (J : Finset ℚ) (hJ : ∀ q ∈ J, 0 ≤ q) :
    ∀ q ∈
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate t J,
      0 ≤ q := by
  intro q hq
  rcases Finset.mem_image.mp hq with ⟨r, hr, rfl⟩
  exact add_nonneg (hJ r hr) ht

/-- Positive rational time translates the canonical finite nonnegative slot index. -/
def primaryScalarFiniteNonnegativeSlotIndexTimeTranslate
    (t : ℚ) (ht : 0 ≤ t)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex) :
    PrimaryScalarFiniteNonnegativeSlotIndex :=
  ⟨periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate t J.1,
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate_nonneg
      t ht J.1 J.2⟩

@[simp]
theorem primaryScalarFiniteNonnegativeSlotIndexTimeTranslate_val
    (t : ℚ) (ht : 0 ≤ t)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex) :
    (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate t ht J).1 =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate t J.1 :=
  rfl

/-- Slot translation respects inclusion of finite slot sets. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate_mono
    (t : ℚ) {J K : Finset ℚ} (hJK : J ⊆ K) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate t J ⊆
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate t K := by
  intro q hq
  rcases Finset.mem_image.mp hq with ⟨r, hr, rfl⟩
  exact Finset.mem_image.mpr ⟨r, hJK hr, rfl⟩

/-- On canonical finite nonnegative slot indices, positive-time translation is monotone. -/
theorem primaryScalarFiniteNonnegativeSlotIndexTimeTranslate_mono
    (t : ℚ) (ht : 0 ≤ t)
    {J K : PrimaryScalarFiniteNonnegativeSlotIndex}
    (hJK : J ≤ K) :
    primaryScalarFiniteNonnegativeSlotIndexTimeTranslate t ht J ≤
      primaryScalarFiniteNonnegativeSlotIndexTimeTranslate t ht K :=
  periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate_mono
    t hJK

/-- The canonical translated-slot member associated with an original slot. -/
def periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslateMember
    (J : Finset ℚ) (t : ℚ) (q : J) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate t J :=
  ⟨q.1 + t, Finset.mem_image.mpr ⟨q.1, q.2, rfl⟩⟩

@[simp]
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslateMember_val
    (J : Finset ℚ) (t : ℚ) (q : J) :
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslateMember
      J t q).1 = q.1 + t :=
  rfl

/-- Coordinate pullback from translated finite slots to the original finite slots. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslateCoordinatePullback
    (J : Finset ℚ) (t : ℚ) :
    C(
      (∀ r :
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate t J,
        ℝ),
      (∀ q : J, ℝ)) :=
  ⟨fun v q =>
      v (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslateMember
        J t q),
    continuous_pi (fun q =>
      continuous_apply
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslateMember
          J t q))⟩

/-- Canonical transport of a fixed-slot bounded-continuous observable to the translated slot set. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
    (J : Finset ℚ) (t : ℚ) :
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservable J →ₗ[ℝ]
      PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservable
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate t J) where
  toFun F :=
    F.compContinuous
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslateCoordinatePullback
        J t)
  map_add' F G := by
    ext v
    rfl
  map_smul' c F := by
    ext v
    rfl

/-- Translating a fixed-slot observable and then pulling it to full paths is exactly the same as
pulling the original observable to full paths and translating the path. -/
@[simp]
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable_timeTranslate
    (J : Finset ℚ) (t : ℚ)
    (F : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservable J)
    (x : ℚ → ℝ) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate t J)
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
          J t F) x =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable J F
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathTimeTranslate t x) := by
  rw [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable_apply,
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable_apply]
  change
    F (fun q : J =>
      x ((periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslateMember
        J t q).1)) =
      F (fun q : J => x (q.1 + t))
  rfl

end

end MathlibAnalytic
end MGAP4D
