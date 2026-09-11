import MGAP4D.MathlibAnalytic.FiniteBoltzmannWeightedProjectiveFirstVariation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- First-variation profile of one finite Boltzmann-weighted sum.  This is the
actual derivative profile, not merely its value at beta zero. -/
def finiteBoltzmannWeightedSumFirstVariationProfile
    {α : Type*} [Fintype α]
    (energy weight : α → ℝ)
    (β : ℝ) : ℝ :=
  ∑ x : α,
    ((-energy x) * Real.exp ((-energy x) * β)) * weight x

/-- A single Boltzmann factor has the expected derivative at every beta. -/
theorem finiteBoltzmannFactor_hasDerivAt
    (energy β : ℝ) :
    HasDerivAt
      (fun t : ℝ => Real.exp ((-energy) * t))
      ((-energy) * Real.exp ((-energy) * β))
      β := by
  have hlinear :
      HasDerivAt (fun t : ℝ => (-energy) * t) (-energy) β := by
    simpa using (hasDerivAt_id (x := β)).const_mul (-energy)
  simpa [mul_comm] using hlinear.exp

/-- The finite first-variation profile is the derivative of the original
Boltzmann sum at every beta. -/
theorem finiteBoltzmannWeightedSum_hasDerivAt
    {α : Type*} [Fintype α]
    (energy weight : α → ℝ)
    (β : ℝ) :
    HasDerivAt
      (finiteBoltzmannWeightedSum energy weight)
      (finiteBoltzmannWeightedSumFirstVariationProfile energy weight β)
      β := by
  unfold finiteBoltzmannWeightedSum
    finiteBoltzmannWeightedSumFirstVariationProfile
  exact HasDerivAt.fun_sum
    (u := Finset.univ)
    (fun x _hx =>
      (finiteBoltzmannFactor_hasDerivAt (energy x) β).mul_const (weight x))

/-- Non-factorial beta-zero second variation of a finite Boltzmann sum. -/
def finiteBoltzmannWeightedSumSecondVariation
    {α : Type*} [Fintype α]
    (energy weight : α → ℝ) : ℝ :=
  ∑ x : α, (energy x) ^ 2 * weight x

/-- Differentiating the first-variation profile at beta zero gives the exact
second energy moment. -/
theorem finiteBoltzmannWeightedSumFirstVariationProfile_hasDerivAt_zero
    {α : Type*} [Fintype α]
    (energy weight : α → ℝ) :
    HasDerivAt
      (finiteBoltzmannWeightedSumFirstVariationProfile energy weight)
      (finiteBoltzmannWeightedSumSecondVariation energy weight)
      0 := by
  unfold finiteBoltzmannWeightedSumFirstVariationProfile
    finiteBoltzmannWeightedSumSecondVariation
  exact HasDerivAt.fun_sum
    (u := Finset.univ)
    (fun x _hx => by
      have h :=
        (finiteBoltzmannFactor_hasDerivAt (energy x) 0).const_mul (-energy x)
      have hw := h.mul_const (weight x)
      simpa [pow_two] using hw)

/-- First-variation profile for a scalar-prefactored finite Boltzmann profile. -/
def finiteBoltzmannWeightedProfileFirstVariationProfile
    {α : Type*} [Fintype α]
    (scale : ℝ)
    (energy weight : α → ℝ)
    (β : ℝ) : ℝ :=
  scale * finiteBoltzmannWeightedSumFirstVariationProfile energy weight β

/-- Exact non-factorial beta-zero second variation of a scalar-prefactored
finite Boltzmann profile. -/
def finiteBoltzmannWeightedProfileSecondVariation
    {α : Type*} [Fintype α]
    (scale : ℝ)
    (energy weight : α → ℝ) : ℝ :=
  scale * finiteBoltzmannWeightedSumSecondVariation energy weight

/-- The scalar-prefactored profile is differentiated by its named first-
variation profile at every beta. -/
theorem finiteBoltzmannWeightedProfile_hasDerivAt
    {α : Type*} [Fintype α]
    (scale : ℝ)
    (energy weight : α → ℝ)
    (β : ℝ) :
    HasDerivAt
      (finiteBoltzmannWeightedProfile scale energy weight)
      (finiteBoltzmannWeightedProfileFirstVariationProfile
        scale energy weight β)
      β := by
  unfold finiteBoltzmannWeightedProfile
    finiteBoltzmannWeightedProfileFirstVariationProfile
  exact (finiteBoltzmannWeightedSum_hasDerivAt energy weight β).const_mul scale

/-- The beta-zero derivative of the named first-variation profile is the exact
second energy moment with the original scalar prefactor. -/
theorem finiteBoltzmannWeightedProfileFirstVariationProfile_hasDerivAt_zero
    {α : Type*} [Fintype α]
    (scale : ℝ)
    (energy weight : α → ℝ) :
    HasDerivAt
      (finiteBoltzmannWeightedProfileFirstVariationProfile scale energy weight)
      (finiteBoltzmannWeightedProfileSecondVariation scale energy weight)
      0 := by
  unfold finiteBoltzmannWeightedProfileFirstVariationProfile
    finiteBoltzmannWeightedProfileSecondVariation
  exact
    (finiteBoltzmannWeightedSumFirstVariationProfile_hasDerivAt_zero
      energy weight).const_mul scale

end

end MathlibAnalytic
end MGAP4D
