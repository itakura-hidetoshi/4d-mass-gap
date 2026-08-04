import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusSpatialSingleLinkOscillation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Spatial translation in a fixed direction is injective. -/
theorem finiteEvenFourTorusSpatialVertexStep_injective
    (H : ℕ)
    (μ : FiniteEvenFourTorusSpatialDirection) :
    Function.Injective (fun v : FiniteEvenFourTorusSpatialVertex H =>
      finiteEvenFourTorusSpatialVertexStep H v μ) := by
  intro v w h
  have hval := congrArg Subtype.val h
  have hstep :
      finiteFourTorusStep (2 * H + 1) v.1 μ.1 =
        finiteFourTorusStep (2 * H + 1) w.1 μ.1 := by
    simpa only [finiteEvenFourTorusSpatialVertexStep_coe] using hval
  apply Subtype.ext
  unfold finiteFourTorusStep at hstep
  exact add_right_cancel hstep

/-- Boundary occurrences of one fixed spatial link.  Retaining an occurrence
position avoids any assumption that a plaquette contains the link only once in
the smallest periodic volume. -/
abbrev FiniteEvenFourTorusSpatialPlaquetteBoundaryOccurrence
    (H : ℕ)
    (e : FiniteEvenFourTorusSpatialLink H) : Type :=
  {pk : FiniteEvenFourTorusSpatialPlaquette H × Fin 4 //
    finiteEvenFourTorusSpatialPlaquetteBoundary H pk.1 pk.2 = e}

/-- The direction complementary to the represented target direction at a
specified boundary position. -/
def finiteEvenFourTorusSpatialPlaquetteBoundaryOccurrenceOtherDirection
    {H : ℕ}
    {e : FiniteEvenFourTorusSpatialLink H}
    (o : FiniteEvenFourTorusSpatialPlaquetteBoundaryOccurrence H e) :
    FiniteEvenFourTorusSpatialDirection :=
  if o.1.2 = 0 ∨ o.1.2 = 2 then
    o.1.1.2.1.2
  else
    o.1.1.2.1.1

/-- Every occurrence is coded by its one of four boundary positions and one of
three spatial directions. -/
def finiteEvenFourTorusSpatialPlaquetteBoundaryOccurrenceCode
    {H : ℕ}
    {e : FiniteEvenFourTorusSpatialLink H}
    (o : FiniteEvenFourTorusSpatialPlaquetteBoundaryOccurrence H e) :
    Fin 4 × FiniteEvenFourTorusSpatialDirection :=
  (o.1.2,
    finiteEvenFourTorusSpatialPlaquetteBoundaryOccurrenceOtherDirection o)

/-- The occurrence code is injective.  At positions zero and three the base
vertex is read off directly; at positions one and two it is recovered using
injectivity of spatial translation. -/
theorem finiteEvenFourTorusSpatialPlaquetteBoundaryOccurrenceCode_injective
    (H : ℕ)
    (e : FiniteEvenFourTorusSpatialLink H) :
    Function.Injective
      (finiteEvenFourTorusSpatialPlaquetteBoundaryOccurrenceCode
        (H := H) (e := e)) := by
  rintro ⟨⟨p, k⟩, hp⟩ ⟨⟨p', k'⟩, hp'⟩ hcode
  have hk : k = k' := congrArg Prod.fst hcode
  subst k'
  have hother :
      finiteEvenFourTorusSpatialPlaquetteBoundaryOccurrenceOtherDirection
          (⟨(p, k), hp⟩ :
            FiniteEvenFourTorusSpatialPlaquetteBoundaryOccurrence H e) =
        finiteEvenFourTorusSpatialPlaquetteBoundaryOccurrenceOtherDirection
          (⟨(p', k), hp'⟩ :
            FiniteEvenFourTorusSpatialPlaquetteBoundaryOccurrence H e) :=
    congrArg Prod.snd hcode
  apply Subtype.ext
  apply Prod.ext
  · fin_cases k
    · simp [finiteEvenFourTorusSpatialPlaquetteBoundary,
        finiteEvenFourTorusSpatialPlaquetteBoundaryOccurrenceOtherDirection] at hp hp' hother
      have hb : (p.1, p.2.1.1) = (p'.1, p'.2.1.1) := hp.trans hp'.symm
      apply Prod.ext
      · exact congrArg Prod.fst hb
      · apply Subtype.ext
        apply Prod.ext
        · exact congrArg Prod.snd hb
        · exact hother
    · simp [finiteEvenFourTorusSpatialPlaquetteBoundary,
        finiteEvenFourTorusSpatialPlaquetteBoundaryOccurrenceOtherDirection] at hp hp' hother
      have hb :
          (finiteEvenFourTorusSpatialVertexStep H p.1 p.2.1.1, p.2.1.2) =
            (finiteEvenFourTorusSpatialVertexStep H p'.1 p'.2.1.1, p'.2.1.2) :=
        hp.trans hp'.symm
      apply Prod.ext
      · have hstep :
            finiteEvenFourTorusSpatialVertexStep H p.1 p'.2.1.1 =
              finiteEvenFourTorusSpatialVertexStep H p'.1 p'.2.1.1 := by
          simpa only [hother] using congrArg Prod.fst hb
        exact finiteEvenFourTorusSpatialVertexStep_injective H p'.2.1.1 hstep
      · apply Subtype.ext
        apply Prod.ext
        · exact hother
        · exact congrArg Prod.snd hb
    · simp [finiteEvenFourTorusSpatialPlaquetteBoundary,
        finiteEvenFourTorusSpatialPlaquetteBoundaryOccurrenceOtherDirection] at hp hp' hother
      have hb :
          (finiteEvenFourTorusSpatialVertexStep H p.1 p.2.1.2, p.2.1.1) =
            (finiteEvenFourTorusSpatialVertexStep H p'.1 p'.2.1.2, p'.2.1.1) :=
        hp.trans hp'.symm
      apply Prod.ext
      · have hstep :
            finiteEvenFourTorusSpatialVertexStep H p.1 p'.2.1.2 =
              finiteEvenFourTorusSpatialVertexStep H p'.1 p'.2.1.2 := by
          simpa only [hother] using congrArg Prod.fst hb
        exact finiteEvenFourTorusSpatialVertexStep_injective H p'.2.1.2 hstep
      · apply Subtype.ext
        apply Prod.ext
        · exact congrArg Prod.snd hb
        · exact hother
    · simp [finiteEvenFourTorusSpatialPlaquetteBoundary,
        finiteEvenFourTorusSpatialPlaquetteBoundaryOccurrenceOtherDirection] at hp hp' hother
      have hb : (p.1, p.2.1.2) = (p'.1, p'.2.1.2) := hp.trans hp'.symm
      apply Prod.ext
      · exact congrArg Prod.fst hb
      · apply Subtype.ext
        apply Prod.ext
        · exact hother
        · exact congrArg Prod.snd hb
  · rfl

/-- There are exactly three non-time directions. -/
theorem finiteEvenFourTorusSpatialDirection_card :
    Fintype.card FiniteEvenFourTorusSpatialDirection = 3 := by
  native_decide

/-- Every fixed spatial link has at most twelve boundary occurrences, uniformly
in the finite side parameter, including the modulus-two exceptional volume. -/
theorem finiteEvenFourTorusSpatialPlaquetteBoundaryOccurrence_card_le_twelve
    (H : ℕ)
    (e : FiniteEvenFourTorusSpatialLink H) :
    Fintype.card
        (FiniteEvenFourTorusSpatialPlaquetteBoundaryOccurrence H e) ≤ 12 := by
  calc
    Fintype.card
        (FiniteEvenFourTorusSpatialPlaquetteBoundaryOccurrence H e) ≤
      Fintype.card (Fin 4 × FiniteEvenFourTorusSpatialDirection) :=
        Fintype.card_le_of_injective
          (finiteEvenFourTorusSpatialPlaquetteBoundaryOccurrenceCode
            (H := H) (e := e))
          (finiteEvenFourTorusSpatialPlaquetteBoundaryOccurrenceCode_injective
            H e)
    _ = 12 := by
      simp [finiteEvenFourTorusSpatialDirection_card]

/-- Choose one boundary occurrence for every plaquette touching a fixed link. -/
noncomputable def finiteEvenFourTorusSpatialTouchingPlaquetteToOccurrence
    (H : ℕ)
    (e : FiniteEvenFourTorusSpatialLink H)
    (p : ↥(finiteEvenFourTorusSpatialPlaquettesTouchingLink H e)) :
    FiniteEvenFourTorusSpatialPlaquetteBoundaryOccurrence H e := by
  have hpTouch :
      FiniteEvenFourTorusSpatialPlaquetteTouchesLink H p.1 e :=
    (finiteEvenFourTorusSpatialPlaquette_mem_touchingLink_iff H e p.1).1 p.2
  exact ⟨(p.1, Classical.choose hpTouch), Classical.choose_spec hpTouch⟩

/-- The chosen-occurrence map is injective because it retains the plaquette. -/
theorem finiteEvenFourTorusSpatialTouchingPlaquetteToOccurrence_injective
    (H : ℕ)
    (e : FiniteEvenFourTorusSpatialLink H) :
    Function.Injective
      (finiteEvenFourTorusSpatialTouchingPlaquetteToOccurrence H e) := by
  intro p q hpq
  apply Subtype.ext
  exact congrArg (fun o => o.1.1) hpq

/-- Uniform all-volume spatial incidence bound.  Twelve is deliberately used
instead of the sharper nondegenerate count so that no hidden `H = 0`
exception remains. -/
theorem finiteEvenFourTorusSpatialPlaquettesTouchingLink_card_le_twelve
    (H : ℕ)
    (e : FiniteEvenFourTorusSpatialLink H) :
    (finiteEvenFourTorusSpatialPlaquettesTouchingLink H e).card ≤ 12 := by
  have hCard :
      Fintype.card
          ↥(finiteEvenFourTorusSpatialPlaquettesTouchingLink H e) ≤
        Fintype.card
          (FiniteEvenFourTorusSpatialPlaquetteBoundaryOccurrence H e) :=
    Fintype.card_le_of_injective
      (finiteEvenFourTorusSpatialTouchingPlaquetteToOccurrence H e)
      (finiteEvenFourTorusSpatialTouchingPlaquetteToOccurrence_injective H e)
  calc
    (finiteEvenFourTorusSpatialPlaquettesTouchingLink H e).card =
        Fintype.card
          ↥(finiteEvenFourTorusSpatialPlaquettesTouchingLink H e) := by
      simp
    _ ≤ Fintype.card
          (FiniteEvenFourTorusSpatialPlaquetteBoundaryOccurrence H e) := hCard
    _ ≤ 12 :=
      finiteEvenFourTorusSpatialPlaquetteBoundaryOccurrence_card_le_twelve H e

/-- The exact local half-weight ratio therefore has a genuinely
volume-independent twelve-plaquette majorant. -/
theorem finiteEvenFourTorusZ2SpatialHalfWeight_le_exp_twelve_mul_replace
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge) :
    finiteEvenFourTorusZ2SpatialHalfWeight
        H β energyIdentity energyNontrivial A ≤
      Real.exp
          (6 * β * (energyNontrivial - energyIdentity)) *
        finiteEvenFourTorusZ2SpatialHalfWeight
          H β energyIdentity energyNontrivial
          (finiteZ2GaugeReplaceCoordinate A e g) := by
  have hLocal :=
    finiteEvenFourTorusZ2SpatialHalfWeight_le_exp_touchingCard_mul_replace
      H β energyIdentity energyNontrivial hβ hEnergy A e g
  have hCardNat :=
    finiteEvenFourTorusSpatialPlaquettesTouchingLink_card_le_twelve H e
  have hCard :
      ((finiteEvenFourTorusSpatialPlaquettesTouchingLink H e).card : ℝ) ≤ 12 := by
    exact_mod_cast hCardNat
  have hSpread : 0 ≤ energyNontrivial - energyIdentity := sub_nonneg.mpr hEnergy
  have hCoef : 0 ≤ β / 2 := by positivity
  have hExpArg :
      (β / 2) *
          ((finiteEvenFourTorusSpatialPlaquettesTouchingLink H e).card : ℝ) *
          (energyNontrivial - energyIdentity) ≤
        6 * β * (energyNontrivial - energyIdentity) := by
    have hmul := mul_le_mul_of_nonneg_left hCard hCoef
    nlinarith
  calc
    finiteEvenFourTorusZ2SpatialHalfWeight
        H β energyIdentity energyNontrivial A ≤
      Real.exp
          ((β / 2) *
            ((finiteEvenFourTorusSpatialPlaquettesTouchingLink H e).card : ℝ) *
            (energyNontrivial - energyIdentity)) *
        finiteEvenFourTorusZ2SpatialHalfWeight
          H β energyIdentity energyNontrivial
          (finiteZ2GaugeReplaceCoordinate A e g) := hLocal
    _ ≤ Real.exp (6 * β * (energyNontrivial - energyIdentity)) *
        finiteEvenFourTorusZ2SpatialHalfWeight
          H β energyIdentity energyNontrivial
          (finiteZ2GaugeReplaceCoordinate A e g) := by
      apply mul_le_mul_of_nonneg_right
      · exact Real.exp_monotone hExpArg
      · exact le_of_lt
          (finiteEvenFourTorusZ2SpatialHalfWeight_pos
            H β energyIdentity energyNontrivial
            (finiteZ2GaugeReplaceCoordinate A e g))

end

end MathlibAnalytic
end MGAP4D
