import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCrossingReflection

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Orientation-corrected plaquette reflection exchanges the positive and
negative open-half plaquette sectors. -/
@[simp]
theorem periodicHypercubicEvenPlaquetteReflection_strictPositive_iff_strictNegative
    (H : ℕ) (p : PeriodicHypercubicEvenPlaquette H) :
    periodicHypercubicEvenStrictPositivePlaquette
        (periodicHypercubicEvenPlaquetteReflection H p) ↔
      periodicHypercubicEvenStrictNegativePlaquette p := by
  unfold periodicHypercubicEvenStrictPositivePlaquette
  unfold periodicHypercubicEvenStrictNegativePlaquette
  rw [periodicHypercubicEvenPlaquetteReflection_strictPositiveSupport_iff]
  exact periodicHypercubicEven_reflectSupport_strictPositive_iff_strictNegative H
    (periodicHypercubicEvenPlaquetteVertices p)

/-- Orientation-corrected plaquette reflection exchanges the negative and
positive open-half plaquette sectors. -/
@[simp]
theorem periodicHypercubicEvenPlaquetteReflection_strictNegative_iff_strictPositive
    (H : ℕ) (p : PeriodicHypercubicEvenPlaquette H) :
    periodicHypercubicEvenStrictNegativePlaquette
        (periodicHypercubicEvenPlaquetteReflection H p) ↔
      periodicHypercubicEvenStrictPositivePlaquette p := by
  unfold periodicHypercubicEvenStrictNegativePlaquette
  unfold periodicHypercubicEvenStrictPositivePlaquette
  rw [periodicHypercubicEvenPlaquetteReflection_strictNegativeSupport_iff]
  exact periodicHypercubicEven_reflectSupport_strictNegative_iff_strictPositive H
    (periodicHypercubicEvenPlaquetteVertices p)

/-- Finite subtype of plaquettes contained in the positive open half-torus. -/
abbrev PeriodicHypercubicEvenStrictPositivePlaquetteLabel (H : ℕ) : Type :=
  {p : PeriodicHypercubicEvenPlaquette H //
    periodicHypercubicEvenStrictPositivePlaquette p}

/-- Finite subtype of plaquettes contained in the negative open half-torus. -/
abbrev PeriodicHypercubicEvenStrictNegativePlaquetteLabel (H : ℕ) : Type :=
  {p : PeriodicHypercubicEvenPlaquette H //
    periodicHypercubicEvenStrictNegativePlaquette p}

noncomputable instance periodicHypercubicEvenStrictPositivePlaquetteLabelFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenStrictPositivePlaquetteLabel H) :=
  Fintype.ofFinite _

noncomputable instance periodicHypercubicEvenStrictNegativePlaquetteLabelFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenStrictNegativePlaquetteLabel H) :=
  Fintype.ofFinite _

/-- Reflection sends every positive-open-half plaquette to a negative-open-half
plaquette. -/
def periodicHypercubicEvenStrictPositivePlaquetteReflection
    (H : ℕ) (p : PeriodicHypercubicEvenStrictPositivePlaquetteLabel H) :
    PeriodicHypercubicEvenStrictNegativePlaquetteLabel H :=
  ⟨periodicHypercubicEvenPlaquetteReflection H p.1,
    (periodicHypercubicEvenPlaquetteReflection_strictNegative_iff_strictPositive
      H p.1).2 p.2⟩

/-- Reflection sends every negative-open-half plaquette to a positive-open-half
plaquette. -/
def periodicHypercubicEvenStrictNegativePlaquetteReflection
    (H : ℕ) (p : PeriodicHypercubicEvenStrictNegativePlaquetteLabel H) :
    PeriodicHypercubicEvenStrictPositivePlaquetteLabel H :=
  ⟨periodicHypercubicEvenPlaquetteReflection H p.1,
    (periodicHypercubicEvenPlaquetteReflection_strictPositive_iff_strictNegative
      H p.1).2 p.2⟩

/-- The two subtype reflection maps are mutually inverse. -/
theorem periodicHypercubicEvenStrictPlaquetteReflection_leftInverse
    (H : ℕ) :
    Function.LeftInverse
      (periodicHypercubicEvenStrictNegativePlaquetteReflection H)
      (periodicHypercubicEvenStrictPositivePlaquetteReflection H) := by
  intro p
  apply Subtype.ext
  exact periodicHypercubicEvenPlaquetteReflection_involutive H p.1

/-- The two subtype reflection maps are mutually inverse. -/
theorem periodicHypercubicEvenStrictPlaquetteReflection_rightInverse
    (H : ℕ) :
    Function.RightInverse
      (periodicHypercubicEvenStrictNegativePlaquetteReflection H)
      (periodicHypercubicEvenStrictPositivePlaquetteReflection H) := by
  intro p
  apply Subtype.ext
  exact periodicHypercubicEvenPlaquetteReflection_involutive H p.1

/-- Reflection gives a canonical equivalence between the positive and negative
open-half plaquette sectors. -/
def periodicHypercubicEvenStrictPositiveNegativePlaquetteEquiv
    (H : ℕ) :
    PeriodicHypercubicEvenStrictPositivePlaquetteLabel H ≃
      PeriodicHypercubicEvenStrictNegativePlaquetteLabel H where
  toFun := periodicHypercubicEvenStrictPositivePlaquetteReflection H
  invFun := periodicHypercubicEvenStrictNegativePlaquetteReflection H
  left_inv := periodicHypercubicEvenStrictPlaquetteReflection_leftInverse H
  right_inv := periodicHypercubicEvenStrictPlaquetteReflection_rightInverse H

/-- The two strict open-half plaquette sectors have exactly the same finite
cardinality. -/
theorem periodicHypercubicEvenStrictPositiveNegativePlaquette_card_eq
    (H : ℕ) :
    Fintype.card (PeriodicHypercubicEvenStrictPositivePlaquetteLabel H) =
      Fintype.card (PeriodicHypercubicEvenStrictNegativePlaquetteLabel H) :=
  Fintype.card_congr
    (periodicHypercubicEvenStrictPositiveNegativePlaquetteEquiv H)

end

end MathlibAnalytic
end MGAP4D
