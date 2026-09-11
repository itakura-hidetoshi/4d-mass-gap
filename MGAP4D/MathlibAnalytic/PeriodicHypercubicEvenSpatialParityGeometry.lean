import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenAllSpatialPlanesZeroMomentumSwap23
import Mathlib.Tactic

/-!
# Spatial parity on the even periodic positive-link lattice

After establishing invariance of the all-spatial zero-momentum plaquette observable under the two
adjacent spatial-axis permutations, the next independent symmetry receipt for a scalar glueball
channel is parity.

Spatial parity fixes Euclidean time and negates all three spatial coordinates.  Because the physical
configuration carrier stores only positively oriented links, a positive spatial link is carried to
a negatively traversed link.  Its canonical positive-link representative therefore starts one
spatial step behind the parity-reflected source, and the corresponding group value is inverted.
Positive time links retain their orientation.

This file constructs only that exact finite-lattice geometry and configuration action, proves all
shift/unshift compatibility and involutivity, and packages parity on the time-zero displacement
carrier.  Plaquette-trace parity invariance is deliberately left to the next layer.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Spatial parity fixes Euclidean time and negates all three spatial coordinates. -/
def periodicHypercubicEvenSpatialParity
    (H : ℕ) (v : PeriodicHypercubicEvenVertex H) :
    PeriodicHypercubicEvenVertex H :=
  fun i => if i = 0 then v i else -v i

@[simp]
theorem periodicHypercubicEvenSpatialParity_time
    (H : ℕ) (v : PeriodicHypercubicEvenVertex H) :
    periodicHypercubicEvenSpatialParity H v 0 = v 0 := by
  simp [periodicHypercubicEvenSpatialParity]

@[simp]
theorem periodicHypercubicEvenSpatialParity_space
    (H : ℕ) (v : PeriodicHypercubicEvenVertex H)
    {i : PeriodicHypercubicAxis} (hi : i ≠ 0) :
    periodicHypercubicEvenSpatialParity H v i = -v i := by
  simp [periodicHypercubicEvenSpatialParity, hi]

/-- Spatial parity is involutive. -/
theorem periodicHypercubicEvenSpatialParity_involutive
    (H : ℕ) :
    Function.Involutive (periodicHypercubicEvenSpatialParity H) := by
  intro v
  funext i
  by_cases hi : i = 0
  · subst i
    simp [periodicHypercubicEvenSpatialParity]
  · simp [periodicHypercubicEvenSpatialParity, hi]

/-- Spatial parity preserves a positive time shift. -/
@[simp]
theorem periodicHypercubicEvenSpatialParity_shift_time
    (H : ℕ) (v : PeriodicHypercubicEvenVertex H) :
    periodicHypercubicEvenSpatialParity H
        (periodicHypercubicShift (PeriodicHypercubicEvenSideLength H) v 0) =
      periodicHypercubicShift (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenSpatialParity H v) 0 := by
  funext i
  fin_cases i <;>
    simp [periodicHypercubicEvenSpatialParity,
      periodicHypercubicShift_apply]

/-- Spatial parity turns a positive spatial shift into one negative spatial shift. -/
@[simp]
theorem periodicHypercubicEvenSpatialParity_shift_spatial
    (H : ℕ) (v : PeriodicHypercubicEvenVertex H)
    {mu : PeriodicHypercubicAxis} (hmu : mu ≠ 0) :
    periodicHypercubicEvenSpatialParity H
        (periodicHypercubicShift (PeriodicHypercubicEvenSideLength H) v mu) =
      periodicHypercubicUnshift (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenSpatialParity H v) mu := by
  funext i
  fin_cases mu <;> fin_cases i <;>
    simp_all [periodicHypercubicEvenSpatialParity,
      periodicHypercubicShift_apply,
      periodicHypercubicUnshift,
      periodicHypercubicUnit] <;>
    ring

/-- Spatial parity turns a negative spatial shift into one positive spatial shift. -/
@[simp]
theorem periodicHypercubicEvenSpatialParity_unshift_spatial
    (H : ℕ) (v : PeriodicHypercubicEvenVertex H)
    {mu : PeriodicHypercubicAxis} (hmu : mu ≠ 0) :
    periodicHypercubicEvenSpatialParity H
        (periodicHypercubicUnshift (PeriodicHypercubicEvenSideLength H) v mu) =
      periodicHypercubicShift (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenSpatialParity H v) mu := by
  funext i
  fin_cases mu <;> fin_cases i <;>
    simp_all [periodicHypercubicEvenSpatialParity,
      periodicHypercubicShift_apply,
      periodicHypercubicUnshift,
      periodicHypercubicUnit] <;>
    ring

/-- Positive-link representative of the spatial-parity image of a physical edge.

Time links keep their positive traversal.  Spatial links reverse traversal, so the positive-link
representative starts one step behind the parity-reflected source. -/
def periodicHypercubicEvenEdgeSpatialParity
    (H : ℕ) (e : PeriodicHypercubicEvenEdge H) :
    PeriodicHypercubicEvenEdge H :=
  if e.2 = 0 then
    (periodicHypercubicEvenSpatialParity H e.1, e.2)
  else
    (periodicHypercubicUnshift (PeriodicHypercubicEvenSideLength H)
      (periodicHypercubicEvenSpatialParity H e.1) e.2, e.2)

@[simp]
theorem periodicHypercubicEvenEdgeSpatialParity_direction
    (H : ℕ) (e : PeriodicHypercubicEvenEdge H) :
    (periodicHypercubicEvenEdgeSpatialParity H e).2 = e.2 := by
  by_cases htime : e.2 = 0 <;>
    simp [periodicHypercubicEvenEdgeSpatialParity, htime]

@[simp]
theorem periodicHypercubicEvenEdgeSpatialParity_time
    (H : ℕ) (v : PeriodicHypercubicEvenVertex H) :
    periodicHypercubicEvenEdgeSpatialParity H (v, 0) =
      (periodicHypercubicEvenSpatialParity H v, 0) := by
  simp [periodicHypercubicEvenEdgeSpatialParity]

@[simp]
theorem periodicHypercubicEvenEdgeSpatialParity_spatial
    (H : ℕ) (e : PeriodicHypercubicEvenEdge H)
    (hspace : e.2 ≠ 0) :
    periodicHypercubicEvenEdgeSpatialParity H e =
      (periodicHypercubicUnshift (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenSpatialParity H e.1) e.2, e.2) := by
  simp [periodicHypercubicEvenEdgeSpatialParity, hspace]

/-- Positive-link spatial parity is involutive. -/
theorem periodicHypercubicEvenEdgeSpatialParity_involutive
    (H : ℕ) :
    Function.Involutive (periodicHypercubicEvenEdgeSpatialParity H) := by
  intro e
  rcases e with ⟨v, mu⟩
  by_cases htime : mu = 0
  · subst mu
    apply Prod.ext
    · simp [periodicHypercubicEvenSpatialParity_involutive H v]
    · rfl
  · apply Prod.ext
    · rw [periodicHypercubicEvenEdgeSpatialParity_spatial H (v, mu) htime]
      rw [periodicHypercubicEvenEdgeSpatialParity_spatial H
        (periodicHypercubicUnshift (PeriodicHypercubicEvenSideLength H)
          (periodicHypercubicEvenSpatialParity H v) mu, mu) htime]
      rw [periodicHypercubicEvenSpatialParity_unshift_spatial H
        (periodicHypercubicEvenSpatialParity H v) htime]
      rw [periodicHypercubicEvenSpatialParity_involutive H v]
      exact periodicHypercubicUnshift_shift
        (PeriodicHypercubicEvenSideLength H) v mu
    · simp [periodicHypercubicEvenEdgeSpatialParity, htime]

/-- Spatial parity of a physical positive-link configuration.  Spatial-link values are inverted
because parity reverses their physical traversal; time-link values are not. -/
def periodicHypercubicEvenConfigurationSpatialParity
    {Gauge : Type*} [Group Gauge]
    (H : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    PeriodicHypercubicEvenEdge H → Gauge :=
  fun e =>
    if e.2 = 0 then
      A (periodicHypercubicEvenEdgeSpatialParity H e)
    else
      (A (periodicHypercubicEvenEdgeSpatialParity H e))⁻¹

@[simp]
theorem periodicHypercubicEvenConfigurationSpatialParity_time
    {Gauge : Type*} [Group Gauge]
    (H : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Gauge)
    (v : PeriodicHypercubicEvenVertex H) :
    periodicHypercubicEvenConfigurationSpatialParity H A (v, 0) =
      A (periodicHypercubicEvenEdgeSpatialParity H (v, 0)) := by
  simp [periodicHypercubicEvenConfigurationSpatialParity]

@[simp]
theorem periodicHypercubicEvenConfigurationSpatialParity_spatial
    {Gauge : Type*} [Group Gauge]
    (H : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Gauge)
    (e : PeriodicHypercubicEvenEdge H)
    (hspace : e.2 ≠ 0) :
    periodicHypercubicEvenConfigurationSpatialParity H A e =
      (A (periodicHypercubicEvenEdgeSpatialParity H e))⁻¹ := by
  simp [periodicHypercubicEvenConfigurationSpatialParity, hspace]

/-- The finite positive-link configuration parity operation is involutive. -/
theorem periodicHypercubicEvenConfigurationSpatialParity_involutive
    {Gauge : Type*} [Group Gauge]
    (H : ℕ) :
    Function.Involutive
      (periodicHypercubicEvenConfigurationSpatialParity (Gauge := Gauge) H) := by
  intro A
  funext e
  simp only [periodicHypercubicEvenConfigurationSpatialParity]
  by_cases htime : e.2 = 0
  · have htime' : (periodicHypercubicEvenEdgeSpatialParity H e).2 = 0 := by
      simpa using htime
    rw [if_pos htime, if_pos htime',
      periodicHypercubicEvenEdgeSpatialParity_involutive H e]
  · have htime' : (periodicHypercubicEvenEdgeSpatialParity H e).2 ≠ 0 := by
      simpa using htime
    rw [if_neg htime, if_neg htime', inv_inv,
      periodicHypercubicEvenEdgeSpatialParity_involutive H e]

/-- Spatial parity preserves the finite carrier of time-zero spatial displacements. -/
def periodicHypercubicEvenSpatialDisplacementParityEquiv
    (H : ℕ) :
    PeriodicHypercubicEvenSpatialDisplacement H ≃
      PeriodicHypercubicEvenSpatialDisplacement H where
  toFun a :=
    ⟨periodicHypercubicEvenSpatialParity H a.1, by simpa using a.2⟩
  invFun a :=
    ⟨periodicHypercubicEvenSpatialParity H a.1, by simpa using a.2⟩
  left_inv a := by
    apply Subtype.ext
    exact periodicHypercubicEvenSpatialParity_involutive H a.1
  right_inv a := by
    apply Subtype.ext
    exact periodicHypercubicEvenSpatialParity_involutive H a.1

@[simp]
theorem periodicHypercubicEvenSpatialDisplacementParityEquiv_apply_val
    (H : ℕ) (a : PeriodicHypercubicEvenSpatialDisplacement H) :
    (periodicHypercubicEvenSpatialDisplacementParityEquiv H a).1 =
      periodicHypercubicEvenSpatialParity H a.1 :=
  rfl

end

end MathlibAnalytic
end MGAP4D
