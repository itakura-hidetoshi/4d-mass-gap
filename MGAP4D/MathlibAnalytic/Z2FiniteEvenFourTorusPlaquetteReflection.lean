import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusTimeReflection
import MGAP4D.MathlibAnalytic.Z2FiniteFourDimensionalTimeSupportReflection
import MGAP4D.MathlibAnalytic.Z2FiniteLatticeWilsonPlaquetteOrbitSideClassification
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A torus plaquette contains the Euclidean-time direction exactly when one
of its two defining directions is `0`. -/
def finiteEvenFourTorusPlaquetteHasTimeDirection
    {H : ℕ} (p : FiniteFourTorusPlaquette (2 * H + 1)) : Prop :=
  finiteFourTorusPlaquetteFirstDirection p = 0 ∨
    finiteFourTorusPlaquetteSecondDirection p = 0

/-- Reflection of a positive time unit step becomes a negative time unit step.
Equivalently, reflecting a vertex shifted one step backward in time gives the
reflected vertex shifted one step forward. -/
theorem finiteEvenFourTorusTimeReflection_sub_timeStep
    (H : ℕ) (v : FiniteEvenFourTorusVertex H) :
    finiteEvenFourTorusTimeReflection H
        (v - finiteFourTorusUnitStep (2 * H + 1) 0) =
      finiteEvenFourTorusTimeReflection H v +
        finiteFourTorusUnitStep (2 * H + 1) 0 := by
  funext i
  by_cases hi : i = 0
  · subst i
    simp [finiteEvenFourTorusTimeReflection, finiteFourTorusUnitStep]
    ring
  · simp [finiteEvenFourTorusTimeReflection,
      finiteFourTorusUnitStep, hi]

/-- Reflected base vertex of a positively oriented torus plaquette.

For a spatial plaquette the reflected base is simply `θv`.  If a time
direction occurs, positive orientation after reflection requires moving the
base one unit backward in Euclidean time. -/
def finiteEvenFourTorusReflectedPlaquetteBase
    (H : ℕ) (p : FiniteFourTorusPlaquette (2 * H + 1)) :
    FiniteEvenFourTorusVertex H := by
  classical
  exact
    if finiteEvenFourTorusPlaquetteHasTimeDirection p then
      finiteEvenFourTorusTimeReflection H
          (finiteFourTorusPlaquetteBase p) -
        finiteFourTorusUnitStep (2 * H + 1) 0
    else
      finiteEvenFourTorusTimeReflection H
        (finiteFourTorusPlaquetteBase p)

/-- Concrete plaquette reflection on the even four-dimensional torus.  The
direction pair is retained while the base vertex is reflected with the
orientation correction above. -/
def finiteEvenFourTorusPlaquetteReflection
    (H : ℕ) (p : FiniteFourTorusPlaquette (2 * H + 1)) :
    FiniteFourTorusPlaquette (2 * H + 1) :=
  (finiteEvenFourTorusReflectedPlaquetteBase H p, p.2)

@[simp]
theorem finiteEvenFourTorusPlaquetteReflection_firstDirection
    (H : ℕ) (p : FiniteFourTorusPlaquette (2 * H + 1)) :
    finiteFourTorusPlaquetteFirstDirection
        (finiteEvenFourTorusPlaquetteReflection H p) =
      finiteFourTorusPlaquetteFirstDirection p := by
  rfl

@[simp]
theorem finiteEvenFourTorusPlaquetteReflection_secondDirection
    (H : ℕ) (p : FiniteFourTorusPlaquette (2 * H + 1)) :
    finiteFourTorusPlaquetteSecondDirection
        (finiteEvenFourTorusPlaquetteReflection H p) =
      finiteFourTorusPlaquetteSecondDirection p := by
  rfl

@[simp]
theorem finiteEvenFourTorusPlaquetteReflection_hasTimeDirection
    (H : ℕ) (p : FiniteFourTorusPlaquette (2 * H + 1)) :
    finiteEvenFourTorusPlaquetteHasTimeDirection
        (finiteEvenFourTorusPlaquetteReflection H p) ↔
      finiteEvenFourTorusPlaquetteHasTimeDirection p := by
  rfl

/-- The reflected plaquette has the reflected base by construction. -/
@[simp]
theorem finiteFourTorusPlaquetteBase_reflection
    (H : ℕ) (p : FiniteFourTorusPlaquette (2 * H + 1)) :
    finiteFourTorusPlaquetteBase
        (finiteEvenFourTorusPlaquetteReflection H p) =
      finiteEvenFourTorusReflectedPlaquetteBase H p := by
  rfl

/-- The orientation-corrected reflected base is involutive. -/
theorem finiteEvenFourTorusReflectedPlaquetteBase_involutive
    (H : ℕ) (p : FiniteFourTorusPlaquette (2 * H + 1)) :
    finiteEvenFourTorusReflectedPlaquetteBase H
        (finiteEvenFourTorusPlaquetteReflection H p) =
      finiteFourTorusPlaquetteBase p := by
  classical
  by_cases ht : finiteEvenFourTorusPlaquetteHasTimeDirection p
  · have htr : finiteEvenFourTorusPlaquetteHasTimeDirection
        (finiteEvenFourTorusPlaquetteReflection H p) :=
      (finiteEvenFourTorusPlaquetteReflection_hasTimeDirection H p).2 ht
    unfold finiteEvenFourTorusReflectedPlaquetteBase
    rw [if_pos htr]
    change finiteEvenFourTorusTimeReflection H
        (finiteEvenFourTorusReflectedPlaquetteBase H p) -
      finiteFourTorusUnitStep (2 * H + 1) 0 =
        finiteFourTorusPlaquetteBase p
    rw [finiteEvenFourTorusReflectedPlaquetteBase]
    rw [if_pos ht]
    rw [finiteEvenFourTorusTimeReflection_sub_timeStep]
    rw [finiteEvenFourTorusTimeReflection_involutive]
    simp
  · have htr : ¬ finiteEvenFourTorusPlaquetteHasTimeDirection
        (finiteEvenFourTorusPlaquetteReflection H p) := by
      intro h
      exact ht
        ((finiteEvenFourTorusPlaquetteReflection_hasTimeDirection H p).1 h)
    unfold finiteEvenFourTorusReflectedPlaquetteBase
    rw [if_neg htr]
    change finiteEvenFourTorusTimeReflection H
        (finiteEvenFourTorusReflectedPlaquetteBase H p) =
      finiteFourTorusPlaquetteBase p
    rw [finiteEvenFourTorusReflectedPlaquetteBase]
    rw [if_neg ht]
    exact finiteEvenFourTorusTimeReflection_involutive H
      (finiteFourTorusPlaquetteBase p)

/-- Plaquette reflection is an involution. -/
theorem finiteEvenFourTorusPlaquetteReflection_involutive
    (H : ℕ) :
    Function.Involutive (finiteEvenFourTorusPlaquetteReflection H) := by
  intro p
  apply Prod.ext
  · exact finiteEvenFourTorusReflectedPlaquetteBase_involutive H p
  · rfl

/-- Concrete plaquette reflection packaged with a finite orbit ranking. -/
def finiteEvenFourTorusPlaquetteOrbitPartition
    (H : ℕ) :
    FiniteInvolutivePlaquetteOrbitPartition
      (FiniteFourTorusPlaquette (2 * H + 1)) :=
  { reflection := finiteEvenFourTorusPlaquetteReflection H
    reflection_involutive :=
      finiteEvenFourTorusPlaquetteReflection_involutive H
    rank := Fintype.equivFin (FiniteFourTorusPlaquette (2 * H + 1)) }

/-- The concrete orbit classifier exchanges positive and negative plaquette
representatives and preserves fixed plaquettes. -/
@[simp]
theorem finiteEvenFourTorusPlaquetteOrbitPartition_side_reflection
    (H : ℕ) (p : FiniteFourTorusPlaquette (2 * H + 1)) :
    (finiteEvenFourTorusPlaquetteOrbitPartition H).side
        (finiteEvenFourTorusPlaquetteReflection H p) =
      match (finiteEvenFourTorusPlaquetteOrbitPartition H).side p with
      | .positive => .negative
      | .crossing => .crossing
      | .negative => .positive := by
  exact
    (finiteEvenFourTorusPlaquetteOrbitPartition H).side_reflection p

end

end MathlibAnalytic
end MGAP4D
