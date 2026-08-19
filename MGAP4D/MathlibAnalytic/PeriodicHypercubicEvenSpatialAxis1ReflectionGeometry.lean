import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialParityGeometry
import Mathlib.Tactic

/-!
# Reflection of one spatial axis on the even periodic positive-link lattice

The adjacent spatial-axis swaps generate ordinary permutations of axes `1,2,3`, but full cubic
signed-permutation symmetry also needs one independent sign flip.  This file constructs reflection
of spatial axis `1` while fixing Euclidean time and spatial axes `2,3`.

Because the physical carrier stores only positively oriented links, a positive axis-`1` link is
sent to a negatively traversed link.  Its canonical positive-link representative therefore starts
one step behind the reflected source and its configuration value is inverted.  Links in all other
directions retain positive traversal.

This is geometry/configuration action only.  No plaquette-trace invariance, full cubic label,
continuum-spin identification, or spectral claim is made here.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Reflection of spatial axis `1`, fixing Euclidean time and spatial axes `2,3`. -/
def periodicHypercubicEvenSpatialAxis1Reflection
    (H : ℕ) (v : PeriodicHypercubicEvenVertex H) :
    PeriodicHypercubicEvenVertex H :=
  fun i => if i = 1 then -v i else v i

@[simp]
theorem periodicHypercubicEvenSpatialAxis1Reflection_axis1
    (H : ℕ) (v : PeriodicHypercubicEvenVertex H) :
    periodicHypercubicEvenSpatialAxis1Reflection H v 1 = -v 1 := by
  simp [periodicHypercubicEvenSpatialAxis1Reflection]

@[simp]
theorem periodicHypercubicEvenSpatialAxis1Reflection_other
    (H : ℕ) (v : PeriodicHypercubicEvenVertex H)
    {i : PeriodicHypercubicAxis} (hi : i ≠ 1) :
    periodicHypercubicEvenSpatialAxis1Reflection H v i = v i := by
  simp [periodicHypercubicEvenSpatialAxis1Reflection, hi]

/-- Single-axis reflection is involutive. -/
theorem periodicHypercubicEvenSpatialAxis1Reflection_involutive
    (H : ℕ) :
    Function.Involutive (periodicHypercubicEvenSpatialAxis1Reflection H) := by
  intro v
  funext i
  by_cases hi : i = 1
  · subst i
    simp [periodicHypercubicEvenSpatialAxis1Reflection]
  · simp [periodicHypercubicEvenSpatialAxis1Reflection, hi]

/-- Reflection turns a positive axis-`1` shift into one negative axis-`1` shift. -/
@[simp]
theorem periodicHypercubicEvenSpatialAxis1Reflection_shift_axis1
    (H : ℕ) (v : PeriodicHypercubicEvenVertex H) :
    periodicHypercubicEvenSpatialAxis1Reflection H
        (periodicHypercubicShift (PeriodicHypercubicEvenSideLength H) v 1) =
      periodicHypercubicUnshift (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenSpatialAxis1Reflection H v) 1 := by
  funext i
  fin_cases i <;>
    simp [periodicHypercubicEvenSpatialAxis1Reflection,
      periodicHypercubicShift_apply,
      periodicHypercubicUnshift, periodicHypercubicUnit] <;>
    ring

/-- Reflection commutes with positive shifts in every direction other than axis `1`. -/
@[simp]
theorem periodicHypercubicEvenSpatialAxis1Reflection_shift_other
    (H : ℕ) (v : PeriodicHypercubicEvenVertex H)
    {mu : PeriodicHypercubicAxis} (hmu : mu ≠ 1) :
    periodicHypercubicEvenSpatialAxis1Reflection H
        (periodicHypercubicShift (PeriodicHypercubicEvenSideLength H) v mu) =
      periodicHypercubicShift (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenSpatialAxis1Reflection H v) mu := by
  funext i
  fin_cases mu <;> fin_cases i <;>
    simp_all [periodicHypercubicEvenSpatialAxis1Reflection,
      periodicHypercubicShift_apply,
      periodicHypercubicUnshift, periodicHypercubicUnit] <;>
    ring

/-- Reflection turns a negative axis-`1` shift into one positive axis-`1` shift. -/
@[simp]
theorem periodicHypercubicEvenSpatialAxis1Reflection_unshift_axis1
    (H : ℕ) (v : PeriodicHypercubicEvenVertex H) :
    periodicHypercubicEvenSpatialAxis1Reflection H
        (periodicHypercubicUnshift (PeriodicHypercubicEvenSideLength H) v 1) =
      periodicHypercubicShift (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenSpatialAxis1Reflection H v) 1 := by
  funext i
  fin_cases i <;>
    simp [periodicHypercubicEvenSpatialAxis1Reflection,
      periodicHypercubicShift_apply,
      periodicHypercubicUnshift, periodicHypercubicUnit] <;>
    ring

/-- Reflection commutes with negative shifts in every direction other than axis `1`. -/
@[simp]
theorem periodicHypercubicEvenSpatialAxis1Reflection_unshift_other
    (H : ℕ) (v : PeriodicHypercubicEvenVertex H)
    {mu : PeriodicHypercubicAxis} (hmu : mu ≠ 1) :
    periodicHypercubicEvenSpatialAxis1Reflection H
        (periodicHypercubicUnshift (PeriodicHypercubicEvenSideLength H) v mu) =
      periodicHypercubicUnshift (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenSpatialAxis1Reflection H v) mu := by
  funext i
  fin_cases mu <;> fin_cases i <;>
    simp_all [periodicHypercubicEvenSpatialAxis1Reflection,
      periodicHypercubicShift_apply,
      periodicHypercubicUnshift, periodicHypercubicUnit] <;>
    ring

/-- Positive-link representative of the image of a physical edge under axis-`1` reflection.

Only direction `1` reverses traversal, so only that direction requires a one-step source shift. -/
def periodicHypercubicEvenEdgeSpatialAxis1Reflection
    (H : ℕ) (e : PeriodicHypercubicEvenEdge H) :
    PeriodicHypercubicEvenEdge H :=
  if e.2 = 1 then
    (periodicHypercubicUnshift (PeriodicHypercubicEvenSideLength H)
      (periodicHypercubicEvenSpatialAxis1Reflection H e.1) e.2, e.2)
  else
    (periodicHypercubicEvenSpatialAxis1Reflection H e.1, e.2)

@[simp]
theorem periodicHypercubicEvenEdgeSpatialAxis1Reflection_direction
    (H : ℕ) (e : PeriodicHypercubicEvenEdge H) :
    (periodicHypercubicEvenEdgeSpatialAxis1Reflection H e).2 = e.2 := by
  by_cases haxis : e.2 = 1 <;>
    simp [periodicHypercubicEvenEdgeSpatialAxis1Reflection, haxis]

@[simp]
theorem periodicHypercubicEvenEdgeSpatialAxis1Reflection_axis1
    (H : ℕ) (v : PeriodicHypercubicEvenVertex H) :
    periodicHypercubicEvenEdgeSpatialAxis1Reflection H (v, 1) =
      (periodicHypercubicUnshift (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenSpatialAxis1Reflection H v) 1, 1) := by
  simp [periodicHypercubicEvenEdgeSpatialAxis1Reflection]

@[simp]
theorem periodicHypercubicEvenEdgeSpatialAxis1Reflection_other
    (H : ℕ) (e : PeriodicHypercubicEvenEdge H)
    (hother : e.2 ≠ 1) :
    periodicHypercubicEvenEdgeSpatialAxis1Reflection H e =
      (periodicHypercubicEvenSpatialAxis1Reflection H e.1, e.2) := by
  simp [periodicHypercubicEvenEdgeSpatialAxis1Reflection, hother]

/-- Positive-link axis-`1` reflection is involutive. -/
theorem periodicHypercubicEvenEdgeSpatialAxis1Reflection_involutive
    (H : ℕ) :
    Function.Involutive (periodicHypercubicEvenEdgeSpatialAxis1Reflection H) := by
  intro e
  rcases e with ⟨v, mu⟩
  by_cases haxis : mu = 1
  · subst mu
    apply Prod.ext
    · rw [periodicHypercubicEvenEdgeSpatialAxis1Reflection_axis1 H v]
      rw [periodicHypercubicEvenEdgeSpatialAxis1Reflection_axis1 H]
      rw [periodicHypercubicEvenSpatialAxis1Reflection_unshift_axis1 H]
      rw [periodicHypercubicEvenSpatialAxis1Reflection_involutive H v]
      exact periodicHypercubicUnshift_shift
        (PeriodicHypercubicEvenSideLength H) v 1
    · rfl
  · apply Prod.ext
    · rw [periodicHypercubicEvenEdgeSpatialAxis1Reflection_other H (v, mu) haxis]
      rw [periodicHypercubicEvenEdgeSpatialAxis1Reflection_other H
        (periodicHypercubicEvenSpatialAxis1Reflection H v, mu) haxis]
      exact periodicHypercubicEvenSpatialAxis1Reflection_involutive H v
    · simp [periodicHypercubicEvenEdgeSpatialAxis1Reflection, haxis]

/-- Axis-`1` reflection of a physical positive-link configuration.  Exactly the axis-`1` link
values are inverted because exactly those physical traversals reverse. -/
def periodicHypercubicEvenConfigurationSpatialAxis1Reflection
    {Gauge : Type*} [Group Gauge]
    (H : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    PeriodicHypercubicEvenEdge H → Gauge :=
  fun e =>
    if e.2 = 1 then
      (A (periodicHypercubicEvenEdgeSpatialAxis1Reflection H e))⁻¹
    else
      A (periodicHypercubicEvenEdgeSpatialAxis1Reflection H e)

@[simp]
theorem periodicHypercubicEvenConfigurationSpatialAxis1Reflection_axis1
    {Gauge : Type*} [Group Gauge]
    (H : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Gauge)
    (v : PeriodicHypercubicEvenVertex H) :
    periodicHypercubicEvenConfigurationSpatialAxis1Reflection H A (v, 1) =
      (A (periodicHypercubicEvenEdgeSpatialAxis1Reflection H (v, 1)))⁻¹ := by
  simp [periodicHypercubicEvenConfigurationSpatialAxis1Reflection]

@[simp]
theorem periodicHypercubicEvenConfigurationSpatialAxis1Reflection_other
    {Gauge : Type*} [Group Gauge]
    (H : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Gauge)
    (e : PeriodicHypercubicEvenEdge H)
    (hother : e.2 ≠ 1) :
    periodicHypercubicEvenConfigurationSpatialAxis1Reflection H A e =
      A (periodicHypercubicEvenEdgeSpatialAxis1Reflection H e) := by
  simp [periodicHypercubicEvenConfigurationSpatialAxis1Reflection, hother]

/-- The finite positive-link configuration axis-`1` reflection is involutive. -/
theorem periodicHypercubicEvenConfigurationSpatialAxis1Reflection_involutive
    {Gauge : Type*} [Group Gauge]
    (H : ℕ) :
    Function.Involutive
      (periodicHypercubicEvenConfigurationSpatialAxis1Reflection (Gauge := Gauge) H) := by
  intro A
  funext e
  simp only [periodicHypercubicEvenConfigurationSpatialAxis1Reflection]
  by_cases haxis : e.2 = 1
  · have haxis' : (periodicHypercubicEvenEdgeSpatialAxis1Reflection H e).2 = 1 := by
      simpa using haxis
    rw [if_pos haxis, if_pos haxis', inv_inv,
      periodicHypercubicEvenEdgeSpatialAxis1Reflection_involutive H e]
  · have haxis' : (periodicHypercubicEvenEdgeSpatialAxis1Reflection H e).2 ≠ 1 := by
      simpa using haxis
    rw [if_neg haxis, if_neg haxis',
      periodicHypercubicEvenEdgeSpatialAxis1Reflection_involutive H e]

/-- Axis-`1` reflection preserves the finite carrier of time-zero spatial displacements. -/
def periodicHypercubicEvenSpatialDisplacementAxis1ReflectionEquiv
    (H : ℕ) :
    PeriodicHypercubicEvenSpatialDisplacement H ≃
      PeriodicHypercubicEvenSpatialDisplacement H where
  toFun a :=
    ⟨periodicHypercubicEvenSpatialAxis1Reflection H a.1,
      by simpa [periodicHypercubicEvenSpatialAxis1Reflection] using a.2⟩
  invFun a :=
    ⟨periodicHypercubicEvenSpatialAxis1Reflection H a.1,
      by simpa [periodicHypercubicEvenSpatialAxis1Reflection] using a.2⟩
  left_inv a := by
    apply Subtype.ext
    exact periodicHypercubicEvenSpatialAxis1Reflection_involutive H a.1
  right_inv a := by
    apply Subtype.ext
    exact periodicHypercubicEvenSpatialAxis1Reflection_involutive H a.1

@[simp]
theorem periodicHypercubicEvenSpatialDisplacementAxis1ReflectionEquiv_apply_val
    (H : ℕ) (a : PeriodicHypercubicEvenSpatialDisplacement H) :
    (periodicHypercubicEvenSpatialDisplacementAxis1ReflectionEquiv H a).1 =
      periodicHypercubicEvenSpatialAxis1Reflection H a.1 :=
  rfl

end

end MathlibAnalytic
end MGAP4D
