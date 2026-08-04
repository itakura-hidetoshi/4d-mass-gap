import MGAP4D.MathlibAnalytic.FiniteZ2GaugeProductKernelLikelihoodRatio
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusSpatialSlice
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Ordered four-link boundary of an actual spatial-slice plaquette. -/
def finiteEvenFourTorusSpatialPlaquetteBoundary
    (H : ℕ)
    (p : FiniteEvenFourTorusSpatialPlaquette H) :
    Fin 4 → FiniteEvenFourTorusSpatialLink H :=
  ![(p.1, p.2.1.1),
    (finiteEvenFourTorusSpatialVertexStep H p.1 p.2.1.1, p.2.1.2),
    (finiteEvenFourTorusSpatialVertexStep H p.1 p.2.1.2, p.2.1.1),
    (p.1, p.2.1.2)]

/-- A spatial plaquette touches a spatial link when the link occurs in its
ordered four-link boundary. -/
def FiniteEvenFourTorusSpatialPlaquetteTouchesLink
    (H : ℕ)
    (p : FiniteEvenFourTorusSpatialPlaquette H)
    (e : FiniteEvenFourTorusSpatialLink H) : Prop :=
  ∃ k : Fin 4, finiteEvenFourTorusSpatialPlaquetteBoundary H p k = e

/-- Finite set of spatial plaquettes touching one spatial link. -/
noncomputable def finiteEvenFourTorusSpatialPlaquettesTouchingLink
    (H : ℕ)
    (e : FiniteEvenFourTorusSpatialLink H) :
    Finset (FiniteEvenFourTorusSpatialPlaquette H) := by
  classical
  exact Finset.univ.filter fun p =>
    FiniteEvenFourTorusSpatialPlaquetteTouchesLink H p e

@[simp] theorem finiteEvenFourTorusSpatialPlaquette_mem_touchingLink_iff
    (H : ℕ)
    (e : FiniteEvenFourTorusSpatialLink H)
    (p : FiniteEvenFourTorusSpatialPlaquette H) :
    p ∈ finiteEvenFourTorusSpatialPlaquettesTouchingLink H e ↔
      FiniteEvenFourTorusSpatialPlaquetteTouchesLink H p e := by
  classical
  simp [finiteEvenFourTorusSpatialPlaquettesTouchingLink]

/-- The spatial plaquette holonomy is determined by the four ordered boundary
link values. -/
theorem finiteEvenFourTorusZ2SpatialPlaquetteHolonomy_congr
    (H : ℕ)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (p : FiniteEvenFourTorusSpatialPlaquette H)
    (hBoundary : ∀ k : Fin 4,
      A (finiteEvenFourTorusSpatialPlaquetteBoundary H p k) =
        B (finiteEvenFourTorusSpatialPlaquetteBoundary H p k)) :
    finiteEvenFourTorusZ2SpatialPlaquetteHolonomy H A p =
      finiteEvenFourTorusZ2SpatialPlaquetteHolonomy H B p := by
  have h0 := hBoundary 0
  have h1 := hBoundary 1
  have h2 := hBoundary 2
  have h3 := hBoundary 3
  simp [finiteEvenFourTorusSpatialPlaquetteBoundary] at h0 h1 h2 h3
  unfold finiteEvenFourTorusZ2SpatialPlaquetteHolonomy
  rw [h0, h1, h2, h3]

/-- Replacing a link outside a plaquette boundary leaves that plaquette's
holonomy unchanged. -/
theorem finiteEvenFourTorusZ2SpatialPlaquetteHolonomy_replace_eq_of_not_touches
    (H : ℕ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge)
    (p : FiniteEvenFourTorusSpatialPlaquette H)
    (hNotTouch : ¬ FiniteEvenFourTorusSpatialPlaquetteTouchesLink H p e) :
    finiteEvenFourTorusZ2SpatialPlaquetteHolonomy H A p =
      finiteEvenFourTorusZ2SpatialPlaquetteHolonomy H
        (finiteZ2GaugeReplaceCoordinate A e g) p := by
  apply finiteEvenFourTorusZ2SpatialPlaquetteHolonomy_congr
  intro k
  have hne : finiteEvenFourTorusSpatialPlaquetteBoundary H p k ≠ e := by
    intro hk
    exact hNotTouch ⟨k, hk⟩
  exact
    (finiteZ2GaugeReplaceCoordinate_noteq
      A e (finiteEvenFourTorusSpatialPlaquetteBoundary H p k) g hne).symm

/-- One spatial plaquette's two-valued Wilson energy. -/
def finiteEvenFourTorusZ2SpatialPlaquetteEnergy
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H)
    (p : FiniteEvenFourTorusSpatialPlaquette H) : ℝ :=
  if finiteEvenFourTorusZ2SpatialPlaquetteHolonomy H A p = 1 then
    energyIdentity
  else
    energyNontrivial

/-- The spatial Wilson action is the sum of the local plaquette-energy terms. -/
theorem finiteEvenFourTorusZ2SpatialWilsonAction_eq_sum_plaquetteEnergy
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2SpatialWilsonAction
        H energyIdentity energyNontrivial A =
      ∑ p : FiniteEvenFourTorusSpatialPlaquette H,
        finiteEvenFourTorusZ2SpatialPlaquetteEnergy
          H energyIdentity energyNontrivial A p := by
  rfl

/-- A non-touching plaquette contributes exactly the same energy after a
single-link replacement. -/
theorem finiteEvenFourTorusZ2SpatialPlaquetteEnergy_replace_eq_of_not_touches
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge)
    (p : FiniteEvenFourTorusSpatialPlaquette H)
    (hNotTouch : ¬ FiniteEvenFourTorusSpatialPlaquetteTouchesLink H p e) :
    finiteEvenFourTorusZ2SpatialPlaquetteEnergy
        H energyIdentity energyNontrivial A p =
      finiteEvenFourTorusZ2SpatialPlaquetteEnergy
        H energyIdentity energyNontrivial
        (finiteZ2GaugeReplaceCoordinate A e g) p := by
  unfold finiteEvenFourTorusZ2SpatialPlaquetteEnergy
  rw [finiteEvenFourTorusZ2SpatialPlaquetteHolonomy_replace_eq_of_not_touches
    H A e g p hNotTouch]

/-- Every individual two-valued spatial plaquette-energy difference is bounded
by the local energy spread. -/
theorem finiteEvenFourTorusZ2SpatialPlaquetteEnergy_abs_sub_le_energySpread
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (p : FiniteEvenFourTorusSpatialPlaquette H) :
    |finiteEvenFourTorusZ2SpatialPlaquetteEnergy
          H energyIdentity energyNontrivial A p -
        finiteEvenFourTorusZ2SpatialPlaquetteEnergy
          H energyIdentity energyNontrivial B p| ≤
      energyNontrivial - energyIdentity := by
  have hA :
      energyIdentity ≤
          finiteEvenFourTorusZ2SpatialPlaquetteEnergy
            H energyIdentity energyNontrivial A p ∧
        finiteEvenFourTorusZ2SpatialPlaquetteEnergy
            H energyIdentity energyNontrivial A p ≤ energyNontrivial := by
    unfold finiteEvenFourTorusZ2SpatialPlaquetteEnergy
    split <;> simp [hEnergy]
  have hB :
      energyIdentity ≤
          finiteEvenFourTorusZ2SpatialPlaquetteEnergy
            H energyIdentity energyNontrivial B p ∧
        finiteEvenFourTorusZ2SpatialPlaquetteEnergy
            H energyIdentity energyNontrivial B p ≤ energyNontrivial := by
    unfold finiteEvenFourTorusZ2SpatialPlaquetteEnergy
    split <;> simp [hEnergy]
  apply abs_sub_le_iff.mpr
  constructor <;> linarith

/-- Exact support decomposition of the spatial action change caused by one
link replacement. -/
theorem finiteEvenFourTorusZ2SpatialWilsonAction_sub_replace_eq_sum_touching
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge) :
    finiteEvenFourTorusZ2SpatialWilsonAction
          H energyIdentity energyNontrivial A -
        finiteEvenFourTorusZ2SpatialWilsonAction
          H energyIdentity energyNontrivial
          (finiteZ2GaugeReplaceCoordinate A e g) =
      ∑ p ∈ finiteEvenFourTorusSpatialPlaquettesTouchingLink H e,
        (finiteEvenFourTorusZ2SpatialPlaquetteEnergy
            H energyIdentity energyNontrivial A p -
          finiteEvenFourTorusZ2SpatialPlaquetteEnergy
            H energyIdentity energyNontrivial
            (finiteZ2GaugeReplaceCoordinate A e g) p) := by
  classical
  rw [finiteEvenFourTorusZ2SpatialWilsonAction_eq_sum_plaquetteEnergy,
    finiteEvenFourTorusZ2SpatialWilsonAction_eq_sum_plaquetteEnergy,
    ← Finset.sum_sub_distrib]
  have hSupport :
      (∑ p ∈ finiteEvenFourTorusSpatialPlaquettesTouchingLink H e,
          (finiteEvenFourTorusZ2SpatialPlaquetteEnergy
              H energyIdentity energyNontrivial A p -
            finiteEvenFourTorusZ2SpatialPlaquetteEnergy
              H energyIdentity energyNontrivial
              (finiteZ2GaugeReplaceCoordinate A e g) p)) =
        ∑ p : FiniteEvenFourTorusSpatialPlaquette H,
          (finiteEvenFourTorusZ2SpatialPlaquetteEnergy
              H energyIdentity energyNontrivial A p -
            finiteEvenFourTorusZ2SpatialPlaquetteEnergy
              H energyIdentity energyNontrivial
              (finiteZ2GaugeReplaceCoordinate A e g) p) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro p _hp hNotMem
    have hNotTouch :
        ¬ FiniteEvenFourTorusSpatialPlaquetteTouchesLink H p e := by
      intro hTouch
      exact hNotMem
        ((finiteEvenFourTorusSpatialPlaquette_mem_touchingLink_iff
          H e p).2 hTouch)
    rw [finiteEvenFourTorusZ2SpatialPlaquetteEnergy_replace_eq_of_not_touches
      H energyIdentity energyNontrivial A e g p hNotTouch]
    ring
  exact hSupport.symm

/-- The one-link spatial action oscillation is bounded by the number of actual
spatial plaquettes touching that link times the local energy spread. -/
theorem finiteEvenFourTorusZ2SpatialWilsonAction_sub_replace_abs_le_touchingCard
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge) :
    |finiteEvenFourTorusZ2SpatialWilsonAction
          H energyIdentity energyNontrivial A -
        finiteEvenFourTorusZ2SpatialWilsonAction
          H energyIdentity energyNontrivial
          (finiteZ2GaugeReplaceCoordinate A e g)| ≤
      ((finiteEvenFourTorusSpatialPlaquettesTouchingLink H e).card : ℝ) *
        (energyNontrivial - energyIdentity) := by
  rw [finiteEvenFourTorusZ2SpatialWilsonAction_sub_replace_eq_sum_touching]
  calc
    |∑ p ∈ finiteEvenFourTorusSpatialPlaquettesTouchingLink H e,
        (finiteEvenFourTorusZ2SpatialPlaquetteEnergy
            H energyIdentity energyNontrivial A p -
          finiteEvenFourTorusZ2SpatialPlaquetteEnergy
            H energyIdentity energyNontrivial
            (finiteZ2GaugeReplaceCoordinate A e g) p)| ≤
      ∑ p ∈ finiteEvenFourTorusSpatialPlaquettesTouchingLink H e,
        |finiteEvenFourTorusZ2SpatialPlaquetteEnergy
            H energyIdentity energyNontrivial A p -
          finiteEvenFourTorusZ2SpatialPlaquetteEnergy
            H energyIdentity energyNontrivial
            (finiteZ2GaugeReplaceCoordinate A e g) p| :=
      finite_abs_sum_le_sum_abs
        (finiteEvenFourTorusSpatialPlaquettesTouchingLink H e)
        (fun p =>
          finiteEvenFourTorusZ2SpatialPlaquetteEnergy
              H energyIdentity energyNontrivial A p -
            finiteEvenFourTorusZ2SpatialPlaquetteEnergy
              H energyIdentity energyNontrivial
              (finiteZ2GaugeReplaceCoordinate A e g) p)
    _ ≤ ∑ _p ∈ finiteEvenFourTorusSpatialPlaquettesTouchingLink H e,
        (energyNontrivial - energyIdentity) := by
      apply Finset.sum_le_sum
      intro p _hp
      exact
        finiteEvenFourTorusZ2SpatialPlaquetteEnergy_abs_sub_le_energySpread
          H energyIdentity energyNontrivial hEnergy A
          (finiteZ2GaugeReplaceCoordinate A e g) p
    _ = ((finiteEvenFourTorusSpatialPlaquettesTouchingLink H e).card : ℝ) *
        (energyNontrivial - energyIdentity) := by
      simp [nsmul_eq_mul]

/-- Consequently the actual spatial half-weight changes by at most an explicit
local exponential factor under one-link replacement. -/
theorem finiteEvenFourTorusZ2SpatialHalfWeight_le_exp_touchingCard_mul_replace
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
          ((β / 2) *
            ((finiteEvenFourTorusSpatialPlaquettesTouchingLink H e).card : ℝ) *
            (energyNontrivial - energyIdentity)) *
        finiteEvenFourTorusZ2SpatialHalfWeight
          H β energyIdentity energyNontrivial
          (finiteZ2GaugeReplaceCoordinate A e g) := by
  let S := finiteEvenFourTorusZ2SpatialWilsonAction
    H energyIdentity energyNontrivial A
  let S' := finiteEvenFourTorusZ2SpatialWilsonAction
    H energyIdentity energyNontrivial
      (finiteZ2GaugeReplaceCoordinate A e g)
  let b :=
    ((finiteEvenFourTorusSpatialPlaquettesTouchingLink H e).card : ℝ) *
      (energyNontrivial - energyIdentity)
  have habs : |S - S'| ≤ b := by
    simpa [S, S', b] using
      finiteEvenFourTorusZ2SpatialWilsonAction_sub_replace_abs_le_touchingCard
        H energyIdentity energyNontrivial hEnergy A e g
  have hdiff : S' - S ≤ b := by
    have hlow := (abs_le.mp habs).1
    linarith
  have hcoef : 0 ≤ β / 2 := by positivity
  have hmul : (β / 2) * (S' - S) ≤ (β / 2) * b :=
    mul_le_mul_of_nonneg_left hdiff hcoef
  unfold finiteEvenFourTorusZ2SpatialHalfWeight
  change Real.exp (-(β / 2) * S) ≤
    Real.exp ((β / 2) * b) * Real.exp (-(β / 2) * S')
  rw [← Real.exp_add]
  apply Real.exp_monotone
  linarith

end

end MathlibAnalytic
end MGAP4D
