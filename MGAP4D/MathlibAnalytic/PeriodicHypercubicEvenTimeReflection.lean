import MGAP4D.MathlibAnalytic.PeriodicHypercubicPlaquetteIncidence
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The even periodic side length used for site reflection: `2(H+1)`. -/
abbrev PeriodicHypercubicEvenSideLength (H : ℕ) : ℕ :=
  2 * (H + 1)

/-- Vertices, physical positive links, and plaquettes of the even periodic
four-dimensional lattice. -/
abbrev PeriodicHypercubicEvenVertex (H : ℕ) : Type :=
  PeriodicHypercubicVertex (PeriodicHypercubicEvenSideLength H)

abbrev PeriodicHypercubicEvenEdge (H : ℕ) : Type :=
  PeriodicHypercubicEdge (PeriodicHypercubicEvenSideLength H)

abbrev PeriodicHypercubicEvenPlaquette (H : ℕ) : Type :=
  PeriodicHypercubicPlaquette (PeriodicHypercubicEvenSideLength H)

/-- Site reflection negates the periodic Euclidean-time coordinate and fixes
all spatial coordinates. -/
def periodicHypercubicEvenTimeReflection
    (H : ℕ) (v : PeriodicHypercubicEvenVertex H) :
    PeriodicHypercubicEvenVertex H :=
  fun i => if i = 0 then -v i else v i

@[simp]
theorem periodicHypercubicEvenTimeReflection_time
    (H : ℕ) (v : PeriodicHypercubicEvenVertex H) :
    periodicHypercubicEvenTimeReflection H v 0 = -v 0 := by
  simp [periodicHypercubicEvenTimeReflection]

@[simp]
theorem periodicHypercubicEvenTimeReflection_space
    (H : ℕ) (v : PeriodicHypercubicEvenVertex H)
    {i : PeriodicHypercubicAxis} (hi : i ≠ 0) :
    periodicHypercubicEvenTimeReflection H v i = v i := by
  simp [periodicHypercubicEvenTimeReflection, hi]

/-- Site reflection is involutive. -/
theorem periodicHypercubicEvenTimeReflection_involutive
    (H : ℕ) :
    Function.Involutive (periodicHypercubicEvenTimeReflection H) := by
  intro v
  funext i
  by_cases hi : i = 0
  · subst i
    simp [periodicHypercubicEvenTimeReflection]
  · simp [periodicHypercubicEvenTimeReflection, hi]

/-- Site reflection commutes with every spatial positive unit shift. -/
@[simp]
theorem periodicHypercubicEvenTimeReflection_shift_spatial
    (H : ℕ) (v : PeriodicHypercubicEvenVertex H)
    {mu : PeriodicHypercubicAxis} (hmu : mu ≠ 0) :
    periodicHypercubicEvenTimeReflection H
        (periodicHypercubicShift (PeriodicHypercubicEvenSideLength H) v mu) =
      periodicHypercubicShift (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenTimeReflection H v) mu := by
  have h0mu : (0 : PeriodicHypercubicAxis) ≠ mu := Ne.symm hmu
  funext i
  by_cases hi : i = 0
  · subst i
    simp [periodicHypercubicEvenTimeReflection,
      periodicHypercubicShift, periodicHypercubicUnit, h0mu]
  · simp [periodicHypercubicEvenTimeReflection,
      periodicHypercubicShift, periodicHypercubicUnit, hi]

/-- Reflection turns a positive time shift into one negative time shift. -/
@[simp]
theorem periodicHypercubicEvenTimeReflection_shift_time
    (H : ℕ) (v : PeriodicHypercubicEvenVertex H) :
    periodicHypercubicEvenTimeReflection H
        (periodicHypercubicShift (PeriodicHypercubicEvenSideLength H) v 0) =
      periodicHypercubicUnshift (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenTimeReflection H v) 0 := by
  funext i
  by_cases hi : i = 0
  · subst i
    simp [periodicHypercubicEvenTimeReflection,
      periodicHypercubicShift, periodicHypercubicUnshift,
      periodicHypercubicUnit]
    ring
  · simp [periodicHypercubicEvenTimeReflection,
      periodicHypercubicShift, periodicHypercubicUnshift,
      periodicHypercubicUnit, hi]

/-- Reflection turns one negative time shift into a positive time shift. -/
@[simp]
theorem periodicHypercubicEvenTimeReflection_unshift_time
    (H : ℕ) (v : PeriodicHypercubicEvenVertex H) :
    periodicHypercubicEvenTimeReflection H
        (periodicHypercubicUnshift (PeriodicHypercubicEvenSideLength H) v 0) =
      periodicHypercubicShift (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenTimeReflection H v) 0 := by
  funext i
  by_cases hi : i = 0
  · subst i
    simp [periodicHypercubicEvenTimeReflection,
      periodicHypercubicShift, periodicHypercubicUnshift,
      periodicHypercubicUnit]
    ring
  · simp [periodicHypercubicEvenTimeReflection,
      periodicHypercubicShift, periodicHypercubicUnshift,
      periodicHypercubicUnit, hi]

/-- A coordinate plaquette contains the Euclidean-time direction exactly when
one of its ordered axes is `0`. -/
def periodicHypercubicEvenPlaquetteHasTimeDirection
    {H : ℕ} (p : PeriodicHypercubicEvenPlaquette H) : Prop :=
  periodicHypercubicPlaquetteFirstAxis p = 0 ∨
    periodicHypercubicPlaquetteSecondAxis p = 0

/-- Reflected base of a positively oriented coordinate plaquette.  A plaquette
containing the time direction receives one backward-time base correction so
that its reflected representative remains positively oriented. -/
def periodicHypercubicEvenReflectedPlaquetteBase
    (H : ℕ) (p : PeriodicHypercubicEvenPlaquette H) :
    PeriodicHypercubicEvenVertex H := by
  classical
  exact
    if periodicHypercubicEvenPlaquetteHasTimeDirection p then
      periodicHypercubicUnshift (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenTimeReflection H p.1) 0
    else
      periodicHypercubicEvenTimeReflection H p.1

/-- Orientation-corrected reflection of a periodic coordinate plaquette. -/
def periodicHypercubicEvenPlaquetteReflection
    (H : ℕ) (p : PeriodicHypercubicEvenPlaquette H) :
    PeriodicHypercubicEvenPlaquette H :=
  (periodicHypercubicEvenReflectedPlaquetteBase H p, p.2)

@[simp]
theorem periodicHypercubicEvenPlaquetteReflection_firstAxis
    (H : ℕ) (p : PeriodicHypercubicEvenPlaquette H) :
    periodicHypercubicPlaquetteFirstAxis
        (periodicHypercubicEvenPlaquetteReflection H p) =
      periodicHypercubicPlaquetteFirstAxis p :=
  rfl

@[simp]
theorem periodicHypercubicEvenPlaquetteReflection_secondAxis
    (H : ℕ) (p : PeriodicHypercubicEvenPlaquette H) :
    periodicHypercubicPlaquetteSecondAxis
        (periodicHypercubicEvenPlaquetteReflection H p) =
      periodicHypercubicPlaquetteSecondAxis p :=
  rfl

@[simp]
theorem periodicHypercubicEvenPlaquetteReflection_hasTimeDirection
    (H : ℕ) (p : PeriodicHypercubicEvenPlaquette H) :
    periodicHypercubicEvenPlaquetteHasTimeDirection
        (periodicHypercubicEvenPlaquetteReflection H p) ↔
      periodicHypercubicEvenPlaquetteHasTimeDirection p :=
  Iff.rfl

/-- The orientation-corrected reflected base is involutive. -/
theorem periodicHypercubicEvenReflectedPlaquetteBase_involutive
    (H : ℕ) (p : PeriodicHypercubicEvenPlaquette H) :
    periodicHypercubicEvenReflectedPlaquetteBase H
        (periodicHypercubicEvenPlaquetteReflection H p) = p.1 := by
  classical
  by_cases ht : periodicHypercubicEvenPlaquetteHasTimeDirection p
  · have htr : periodicHypercubicEvenPlaquetteHasTimeDirection
        (periodicHypercubicEvenPlaquetteReflection H p) :=
      (periodicHypercubicEvenPlaquetteReflection_hasTimeDirection H p).2 ht
    unfold periodicHypercubicEvenReflectedPlaquetteBase
    rw [if_pos htr]
    change periodicHypercubicUnshift (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenTimeReflection H
          (periodicHypercubicEvenReflectedPlaquetteBase H p)) 0 = p.1
    rw [periodicHypercubicEvenReflectedPlaquetteBase, if_pos ht]
    rw [periodicHypercubicEvenTimeReflection_unshift_time]
    rw [periodicHypercubicEvenTimeReflection_involutive]
    exact periodicHypercubicUnshift_shift
      (PeriodicHypercubicEvenSideLength H) p.1 0
  · have htr : ¬ periodicHypercubicEvenPlaquetteHasTimeDirection
        (periodicHypercubicEvenPlaquetteReflection H p) := by
      intro h
      exact ht
        ((periodicHypercubicEvenPlaquetteReflection_hasTimeDirection H p).1 h)
    unfold periodicHypercubicEvenReflectedPlaquetteBase
    rw [if_neg htr]
    change periodicHypercubicEvenTimeReflection H
        (periodicHypercubicEvenReflectedPlaquetteBase H p) = p.1
    rw [periodicHypercubicEvenReflectedPlaquetteBase, if_neg ht]
    exact periodicHypercubicEvenTimeReflection_involutive H p.1

/-- Orientation-corrected plaquette reflection is an involution. -/
theorem periodicHypercubicEvenPlaquetteReflection_involutive
    (H : ℕ) :
    Function.Involutive (periodicHypercubicEvenPlaquetteReflection H) := by
  intro p
  apply Prod.ext
  · exact periodicHypercubicEvenReflectedPlaquetteBase_involutive H p
  · rfl

end

end MathlibAnalytic
end MGAP4D
