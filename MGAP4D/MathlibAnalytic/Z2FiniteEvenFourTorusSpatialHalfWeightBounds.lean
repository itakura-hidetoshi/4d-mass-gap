import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusSpatialSlice
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Real-valued number of spatial plaquettes in the canonical finite slice. -/
def finiteEvenFourTorusSpatialPlaquetteCountReal
    (H : ℕ) : ℝ :=
  Fintype.card (FiniteEvenFourTorusSpatialPlaquette H)

/-- The spatial Wilson action is bounded below by assigning the identity energy
to every spatial plaquette. -/
theorem finiteEvenFourTorusZ2SpatialWilsonAction_lower
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusSpatialPlaquetteCountReal H * energyIdentity ≤
      finiteEvenFourTorusZ2SpatialWilsonAction
        H energyIdentity energyNontrivial A := by
  unfold finiteEvenFourTorusSpatialPlaquetteCountReal
    finiteEvenFourTorusZ2SpatialWilsonAction
  calc
    (Fintype.card (FiniteEvenFourTorusSpatialPlaquette H) : ℝ) *
        energyIdentity =
      ∑ _p : FiniteEvenFourTorusSpatialPlaquette H, energyIdentity := by
        simp
    _ ≤ ∑ p : FiniteEvenFourTorusSpatialPlaquette H,
        if finiteEvenFourTorusZ2SpatialPlaquetteHolonomy H A p = 1 then
          energyIdentity
        else
          energyNontrivial := by
      apply Finset.sum_le_sum
      intro p _hp
      by_cases h : finiteEvenFourTorusZ2SpatialPlaquetteHolonomy H A p = 1
      · simp [h]
      · simp [h, hEnergy]

/-- The spatial Wilson action is bounded above by assigning the nontrivial
energy to every spatial plaquette. -/
theorem finiteEvenFourTorusZ2SpatialWilsonAction_upper
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2SpatialWilsonAction
        H energyIdentity energyNontrivial A ≤
      finiteEvenFourTorusSpatialPlaquetteCountReal H * energyNontrivial := by
  unfold finiteEvenFourTorusSpatialPlaquetteCountReal
    finiteEvenFourTorusZ2SpatialWilsonAction
  calc
    (∑ p : FiniteEvenFourTorusSpatialPlaquette H,
        if finiteEvenFourTorusZ2SpatialPlaquetteHolonomy H A p = 1 then
          energyIdentity
        else
          energyNontrivial) ≤
      ∑ _p : FiniteEvenFourTorusSpatialPlaquette H, energyNontrivial := by
        apply Finset.sum_le_sum
        intro p _hp
        by_cases h : finiteEvenFourTorusZ2SpatialPlaquetteHolonomy H A p = 1
        · simp [h, hEnergy]
        · simp [h]
    _ = (Fintype.card (FiniteEvenFourTorusSpatialPlaquette H) : ℝ) *
        energyNontrivial := by
      simp

/-- Uniform lower envelope of the spatial half-weight at one specified finite
volume. -/
def finiteEvenFourTorusZ2SpatialHalfWeightLowerBound
    (H : ℕ)
    (β energyNontrivial : ℝ) : ℝ :=
  Real.exp
    (-(β / 2) *
      (finiteEvenFourTorusSpatialPlaquetteCountReal H * energyNontrivial))

/-- Uniform upper envelope of the spatial half-weight at one specified finite
volume. -/
def finiteEvenFourTorusZ2SpatialHalfWeightUpperBound
    (H : ℕ)
    (β energyIdentity : ℝ) : ℝ :=
  Real.exp
    (-(β / 2) *
      (finiteEvenFourTorusSpatialPlaquetteCountReal H * energyIdentity))

/-- The lower half-weight envelope is strictly positive. -/
theorem finiteEvenFourTorusZ2SpatialHalfWeightLowerBound_pos
    (H : ℕ)
    (β energyNontrivial : ℝ) :
    0 < finiteEvenFourTorusZ2SpatialHalfWeightLowerBound
      H β energyNontrivial :=
  Real.exp_pos _

/-- The upper half-weight envelope is strictly positive. -/
theorem finiteEvenFourTorusZ2SpatialHalfWeightUpperBound_pos
    (H : ℕ)
    (β energyIdentity : ℝ) :
    0 < finiteEvenFourTorusZ2SpatialHalfWeightUpperBound
      H β energyIdentity :=
  Real.exp_pos _

/-- Every finite-volume spatial half-weight is bounded below by the explicit
all-nontrivial-plaquette envelope. -/
theorem finiteEvenFourTorusZ2SpatialHalfWeightLowerBound_le
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2SpatialHalfWeightLowerBound
        H β energyNontrivial ≤
      finiteEvenFourTorusZ2SpatialHalfWeight
        H β energyIdentity energyNontrivial A := by
  unfold finiteEvenFourTorusZ2SpatialHalfWeightLowerBound
    finiteEvenFourTorusZ2SpatialHalfWeight
  apply Real.exp_monotone
  have hAction := finiteEvenFourTorusZ2SpatialWilsonAction_upper
    H energyIdentity energyNontrivial hEnergy A
  have hcoef : 0 ≤ β / 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hAction hcoef
  linarith

/-- Every finite-volume spatial half-weight is bounded above by the explicit
all-identity-plaquette envelope. -/
theorem finiteEvenFourTorusZ2SpatialHalfWeight_le_UpperBound
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2SpatialHalfWeight
        H β energyIdentity energyNontrivial A ≤
      finiteEvenFourTorusZ2SpatialHalfWeightUpperBound
        H β energyIdentity := by
  unfold finiteEvenFourTorusZ2SpatialHalfWeightUpperBound
    finiteEvenFourTorusZ2SpatialHalfWeight
  apply Real.exp_monotone
  have hAction := finiteEvenFourTorusZ2SpatialWilsonAction_lower
    H energyIdentity energyNontrivial hEnergy A
  have hcoef : 0 ≤ β / 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hAction hcoef
  linarith

/-- Explicit finite-volume oscillation ratio of the two global spatial
half-weight envelopes. -/
def finiteEvenFourTorusZ2SpatialHalfWeightOscillationRatio
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ) : ℝ :=
  finiteEvenFourTorusZ2SpatialHalfWeightUpperBound
      H β energyIdentity /
    finiteEvenFourTorusZ2SpatialHalfWeightLowerBound
      H β energyNontrivial

/-- The global half-weight oscillation ratio is exactly exponential in the
number of spatial plaquettes and the local energy spread. -/
theorem finiteEvenFourTorusZ2SpatialHalfWeightOscillationRatio_eq_exp
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ) :
    finiteEvenFourTorusZ2SpatialHalfWeightOscillationRatio
        H β energyIdentity energyNontrivial =
      Real.exp
        ((β / 2) * finiteEvenFourTorusSpatialPlaquetteCountReal H *
          (energyNontrivial - energyIdentity)) := by
  unfold finiteEvenFourTorusZ2SpatialHalfWeightOscillationRatio
    finiteEvenFourTorusZ2SpatialHalfWeightUpperBound
    finiteEvenFourTorusZ2SpatialHalfWeightLowerBound
  rw [← Real.exp_sub]
  congr 1
  ring

/-- Under the monotone-energy and nonnegative-coupling assumptions, the global
oscillation ratio is at least one. -/
theorem one_le_finiteEvenFourTorusZ2SpatialHalfWeightOscillationRatio
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    1 ≤ finiteEvenFourTorusZ2SpatialHalfWeightOscillationRatio
      H β energyIdentity energyNontrivial := by
  rw [finiteEvenFourTorusZ2SpatialHalfWeightOscillationRatio_eq_exp]
  apply Real.one_le_exp
  exact mul_nonneg
    (mul_nonneg (by positivity)
      (by positivity : 0 ≤ finiteEvenFourTorusSpatialPlaquetteCountReal H))
    (sub_nonneg.mpr hEnergy)

end

end MathlibAnalytic
end MGAP4D
