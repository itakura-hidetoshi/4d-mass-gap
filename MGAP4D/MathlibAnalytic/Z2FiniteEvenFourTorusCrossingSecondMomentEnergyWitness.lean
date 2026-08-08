import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossingSecondMomentCountWitness
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The zero/one crossing action is exactly the real cast of the nontrivial
plaquette count. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeCrossingAction_zero_one_eq_count
    (H : ℕ)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeCrossingAction H 0 0 1 U A B =
      (finiteEvenFourTorusZ2CrossingNontrivialCount H U A B : ℝ) := by
  rw [finiteEvenFourTorusZ2UnfixedGaugeCrossingAction_eq_fintype_sum]
  unfold finiteEvenFourTorusZ2CrossingNontrivialCount
    finiteEvenFourTorusZ2CrossingLocalEnergy
  push_cast
  apply Finset.sum_congr rfl
  intro e _he
  by_cases h :
      finiteEvenFourTorusZ2UnfixedTemporalPlaquetteHolonomy H U A B e = 1
  · simp [h]
  · simp [h]

/-- Exact affine dependence of the temporal crossing action on the two physical
energy levels.  All boundary dependence is carried by the integer nontrivial
plaquette count. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeCrossingAction_eq_card_mul_identity_add_count_mul_gap
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeCrossingAction
        H 0 energyIdentity energyNontrivial U A B =
      (Fintype.card (FiniteEvenFourTorusSpatialLink H) : ℝ) * energyIdentity +
        (finiteEvenFourTorusZ2CrossingNontrivialCount H U A B : ℝ) *
          (energyNontrivial - energyIdentity) := by
  rw [finiteEvenFourTorusZ2UnfixedGaugeCrossingAction_eq_fintype_sum]
  unfold finiteEvenFourTorusZ2CrossingNontrivialCount
    finiteEvenFourTorusZ2CrossingLocalEnergy
  push_cast
  calc
    (∑ e : FiniteEvenFourTorusSpatialLink H,
        if finiteEvenFourTorusZ2UnfixedTemporalPlaquetteHolonomy H U A B e = 1
        then energyIdentity else energyNontrivial) =
      ∑ e : FiniteEvenFourTorusSpatialLink H,
        (energyIdentity +
          (if finiteEvenFourTorusZ2UnfixedTemporalPlaquetteHolonomy H U A B e = 1
           then (0 : ℝ) else 1) * (energyNontrivial - energyIdentity)) := by
      apply Finset.sum_congr rfl
      intro e _he
      by_cases h :
          finiteEvenFourTorusZ2UnfixedTemporalPlaquetteHolonomy H U A B e = 1
      · simp [h]
      · simp [h]
    _ = (Fintype.card (FiniteEvenFourTorusSpatialLink H) : ℝ) * energyIdentity +
        (∑ e : FiniteEvenFourTorusSpatialLink H,
          (if finiteEvenFourTorusZ2UnfixedTemporalPlaquetteHolonomy H U A B e = 1
           then (0 : ℝ) else 1)) * (energyNontrivial - energyIdentity) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      rw [Finset.sum_mul]

/-- Compact algebraic engine for the side-two witness.  If four finite real
profiles have zero first mixed sum and squared mixed excess `2 * |γ|`, then the
same four profiles inserted into one common affine energy expression have
uniform mixed square defect exactly `2 * d^2`. -/
theorem finiteUniformAffineSquare_mixedDifference_eq_two_mul_sq
    {γ : Type*} [Fintype γ] [Nonempty γ]
    (N00 N01 N10 N11 : γ → ℝ)
    (a d : ℝ)
    (hFirst :
      (∑ u : γ, N00 u) + (∑ u : γ, N11 u) =
        (∑ u : γ, N01 u) + (∑ u : γ, N10 u))
    (hSecond :
      (∑ u : γ, (N00 u) ^ 2) + (∑ u : γ, (N11 u) ^ 2) =
        (∑ u : γ, (N01 u) ^ 2) + (∑ u : γ, (N10 u) ^ 2) +
          2 * (Fintype.card γ : ℝ)) :
    (Fintype.card γ : ℝ)⁻¹ * (∑ u : γ, (a + N00 u * d) ^ 2) -
        (Fintype.card γ : ℝ)⁻¹ * (∑ u : γ, (a + N01 u * d) ^ 2) -
      ((Fintype.card γ : ℝ)⁻¹ * (∑ u : γ, (a + N10 u * d) ^ 2) -
        (Fintype.card γ : ℝ)⁻¹ * (∑ u : γ, (a + N11 u * d) ^ 2)) =
      2 * d ^ 2 := by
  let n : ℝ := Fintype.card γ
  have hn : n ≠ 0 := by
    dsimp [n]
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card γ ≠ 0)
  change
    n⁻¹ * (∑ u : γ, (a + N00 u * d) ^ 2) -
        n⁻¹ * (∑ u : γ, (a + N01 u * d) ^ 2) -
      (n⁻¹ * (∑ u : γ, (a + N10 u * d) ^ 2) -
        n⁻¹ * (∑ u : γ, (a + N11 u * d) ^ 2)) = 2 * d ^ 2
  simp_rw [show ∀ z : ℝ,
      (a + z * d) ^ 2 = a ^ 2 + (2 * a * d) * z + d ^ 2 * z ^ 2 by
    intro z
    ring]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  field_simp [hn]
  linear_combination
    (2 * a * d) * hFirst + d ^ 2 * hSecond

/-- The explicit side-two finite Wilson witness has exact temporal-crossing
second-moment mixed defect

`2 * (energyNontrivial - energyIdentity)^2`.

The first-count terms cancel, while the squared-count covariance contributes
exactly two after uniform temporal-link averaging. -/
theorem finiteEvenFourTorusZ2TemporalCrossingSecondMoment_mixedDifference_witness_zero
    (energyIdentity energyNontrivial : ℝ) :
    finiteKernelMixedCrossDifference
      (finiteEvenFourTorusZ2TemporalCrossingSecondMoment
        0 energyIdentity energyNontrivial)
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation =
        2 * (energyNontrivial - energyIdentity) ^ 2 := by
  let γ := FiniteEvenFourTorusZ2TemporalLinkField 0
  let N00 : γ → ℕ := fun U =>
    finiteEvenFourTorusZ2CrossingNontrivialCount 0 U
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity
  let N01 : γ → ℕ := fun U =>
    finiteEvenFourTorusZ2CrossingNontrivialCount 0 U
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation
  let N10 : γ → ℕ := fun U =>
    finiteEvenFourTorusZ2CrossingNontrivialCount 0 U
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity
  let N11 : γ → ℕ := fun U =>
    finiteEvenFourTorusZ2CrossingNontrivialCount 0 U
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation
  let R00 : γ → ℝ := fun U => (N00 U : ℝ)
  let R01 : γ → ℝ := fun U => (N01 U : ℝ)
  let R10 : γ → ℝ := fun U => (N10 U : ℝ)
  let R11 : γ → ℝ := fun U => (N11 U : ℝ)
  have hFirstNat :=
    finiteEvenFourTorusZ2CrossingNontrivialCount_sum_mixed_balance_zero
  have hSecondNat :=
    finiteEvenFourTorusZ2CrossingNontrivialCount_sq_sum_mixed_excess_zero
  have hFirst := congrArg (fun z : ℕ => (z : ℝ)) hFirstNat
  have hSecond := congrArg (fun z : ℕ => (z : ℝ)) hSecondNat
  push_cast at hFirst hSecond
  change
    (∑ U : γ, R00 U) + (∑ U : γ, R11 U) =
      (∑ U : γ, R01 U) + (∑ U : γ, R10 U) at hFirst
  change
    (∑ U : γ, (R00 U) ^ 2) + (∑ U : γ, (R11 U) ^ 2) =
      (∑ U : γ, (R01 U) ^ 2) + (∑ U : γ, (R10 U) ^ 2) +
        2 * (Fintype.card γ : ℝ) at hSecond
  unfold finiteKernelMixedCrossDifference
    finiteEvenFourTorusZ2TemporalCrossingSecondMoment
    finiteUniformCrossingSecondMoment
  simp_rw [finiteEvenFourTorusZ2UnfixedGaugeCrossingAction_eq_card_mul_identity_add_count_mul_gap]
  change
    (Fintype.card γ : ℝ)⁻¹ *
          (∑ U : γ,
            ((Fintype.card (FiniteEvenFourTorusSpatialLink 0) : ℝ) * energyIdentity +
              R00 U * (energyNontrivial - energyIdentity)) ^ 2) -
        (Fintype.card γ : ℝ)⁻¹ *
          (∑ U : γ,
            ((Fintype.card (FiniteEvenFourTorusSpatialLink 0) : ℝ) * energyIdentity +
              R01 U * (energyNontrivial - energyIdentity)) ^ 2) -
      ((Fintype.card γ : ℝ)⁻¹ *
          (∑ U : γ,
            ((Fintype.card (FiniteEvenFourTorusSpatialLink 0) : ℝ) * energyIdentity +
              R10 U * (energyNontrivial - energyIdentity)) ^ 2) -
        (Fintype.card γ : ℝ)⁻¹ *
          (∑ U : γ,
            ((Fintype.card (FiniteEvenFourTorusSpatialLink 0) : ℝ) * energyIdentity +
              R11 U * (energyNontrivial - energyIdentity)) ^ 2)) =
      2 * (energyNontrivial - energyIdentity) ^ 2
  exact finiteUniformAffineSquare_mixedDifference_eq_two_mul_sq
    R00 R01 R10 R11
    ((Fintype.card (FiniteEvenFourTorusSpatialLink 0) : ℝ) * energyIdentity)
    (energyNontrivial - energyIdentity)
    hFirst hSecond

/-- Under the strict physical energy ordering, the side-two crossing-second-
moment mixed defect is nonzero. -/
theorem finiteEvenFourTorusZ2TemporalCrossingSecondMoment_mixedDifference_witness_zero_ne_zero
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial) :
    finiteKernelMixedCrossDifference
      (finiteEvenFourTorusZ2TemporalCrossingSecondMoment
        0 energyIdentity energyNontrivial)
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation ≠ 0 := by
  rw [finiteEvenFourTorusZ2TemporalCrossingSecondMoment_mixedDifference_witness_zero]
  have hgap : energyNontrivial - energyIdentity ≠ 0 := sub_ne_zero.mpr (ne_of_gt hEnergy)
  positivity

end

end MathlibAnalytic
end MGAP4D
