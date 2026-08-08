import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossingSecondMomentCountWitness
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

set_option maxHeartbeats 1000000

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
      ring

/-- Real-valued form of the side-two first-count mixed balance. -/
theorem finiteEvenFourTorusZ2CrossingNontrivialCount_real_sum_mixed_balance_zero :
    (∑ U : FiniteEvenFourTorusZ2TemporalLinkField 0,
        (finiteEvenFourTorusZ2CrossingNontrivialCount 0 U
          finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity
          finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity : ℝ)) +
      (∑ U : FiniteEvenFourTorusZ2TemporalLinkField 0,
        (finiteEvenFourTorusZ2CrossingNontrivialCount 0 U
          finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation
          finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation : ℝ)) =
    (∑ U : FiniteEvenFourTorusZ2TemporalLinkField 0,
        (finiteEvenFourTorusZ2CrossingNontrivialCount 0 U
          finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity
          finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation : ℝ)) +
      (∑ U : FiniteEvenFourTorusZ2TemporalLinkField 0,
        (finiteEvenFourTorusZ2CrossingNontrivialCount 0 U
          finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation
          finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity : ℝ)) := by
  exact_mod_cast
    finiteEvenFourTorusZ2CrossingNontrivialCount_sum_mixed_balance_zero

/-- Real-valued form of the side-two squared-count mixed excess. -/
theorem finiteEvenFourTorusZ2CrossingNontrivialCount_real_sq_sum_mixed_excess_zero :
    (∑ U : FiniteEvenFourTorusZ2TemporalLinkField 0,
        (finiteEvenFourTorusZ2CrossingNontrivialCount 0 U
          finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity
          finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity : ℝ) ^ 2) +
      (∑ U : FiniteEvenFourTorusZ2TemporalLinkField 0,
        (finiteEvenFourTorusZ2CrossingNontrivialCount 0 U
          finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation
          finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation : ℝ) ^ 2) =
    (∑ U : FiniteEvenFourTorusZ2TemporalLinkField 0,
        (finiteEvenFourTorusZ2CrossingNontrivialCount 0 U
          finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity
          finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation : ℝ) ^ 2) +
      (∑ U : FiniteEvenFourTorusZ2TemporalLinkField 0,
        (finiteEvenFourTorusZ2CrossingNontrivialCount 0 U
          finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation
          finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity : ℝ) ^ 2) +
      2 * (Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField 0) : ℝ) := by
  exact_mod_cast
    finiteEvenFourTorusZ2CrossingNontrivialCount_sq_sum_mixed_excess_zero

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
  let m : ℝ := Fintype.card (FiniteEvenFourTorusSpatialLink 0)
  let n : ℝ := Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField 0)
  let d : ℝ := energyNontrivial - energyIdentity
  have hn : n ≠ 0 := by
    dsimp [n]
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField 0) ≠ 0)
  have hfirst :=
    finiteEvenFourTorusZ2CrossingNontrivialCount_real_sum_mixed_balance_zero
  have hsecond :=
    finiteEvenFourTorusZ2CrossingNontrivialCount_real_sq_sum_mixed_excess_zero
  unfold finiteKernelMixedCrossDifference
    finiteEvenFourTorusZ2TemporalCrossingSecondMoment
    finiteUniformCrossingSecondMoment
  simp_rw [finiteEvenFourTorusZ2UnfixedGaugeCrossingAction_eq_card_mul_identity_add_count_mul_gap]
  change
    n⁻¹ *
          (∑ U : FiniteEvenFourTorusZ2TemporalLinkField 0,
            (m * energyIdentity +
              (finiteEvenFourTorusZ2CrossingNontrivialCount 0 U
                finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity
                finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity : ℝ) * d) ^ 2) -
        n⁻¹ *
          (∑ U : FiniteEvenFourTorusZ2TemporalLinkField 0,
            (m * energyIdentity +
              (finiteEvenFourTorusZ2CrossingNontrivialCount 0 U
                finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity
                finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation : ℝ) * d) ^ 2) -
      (n⁻¹ *
          (∑ U : FiniteEvenFourTorusZ2TemporalLinkField 0,
            (m * energyIdentity +
              (finiteEvenFourTorusZ2CrossingNontrivialCount 0 U
                finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation
                finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity : ℝ) * d) ^ 2) -
        n⁻¹ *
          (∑ U : FiniteEvenFourTorusZ2TemporalLinkField 0,
            (m * energyIdentity +
              (finiteEvenFourTorusZ2CrossingNontrivialCount 0 U
                finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation
                finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation : ℝ) * d) ^ 2)) =
      2 * d ^ 2
  simp_rw [show ∀ a : ℝ,
      (m * energyIdentity + a * d) ^ 2 =
        (m * energyIdentity) ^ 2 +
          (2 * m * energyIdentity * d) * a + d ^ 2 * a ^ 2 by
    intro a
    ring]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  have hfirst' :
      (∑ U : FiniteEvenFourTorusZ2TemporalLinkField 0,
          (finiteEvenFourTorusZ2CrossingNontrivialCount 0 U
            finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity
            finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity : ℝ)) +
        (∑ U : FiniteEvenFourTorusZ2TemporalLinkField 0,
          (finiteEvenFourTorusZ2CrossingNontrivialCount 0 U
            finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation
            finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation : ℝ)) =
      (∑ U : FiniteEvenFourTorusZ2TemporalLinkField 0,
          (finiteEvenFourTorusZ2CrossingNontrivialCount 0 U
            finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity
            finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation : ℝ)) +
        (∑ U : FiniteEvenFourTorusZ2TemporalLinkField 0,
          (finiteEvenFourTorusZ2CrossingNontrivialCount 0 U
            finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation
            finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity : ℝ)) := hfirst
  have hsecond' :
      (∑ U : FiniteEvenFourTorusZ2TemporalLinkField 0,
          (finiteEvenFourTorusZ2CrossingNontrivialCount 0 U
            finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity
            finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity : ℝ) ^ 2) +
        (∑ U : FiniteEvenFourTorusZ2TemporalLinkField 0,
          (finiteEvenFourTorusZ2CrossingNontrivialCount 0 U
            finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation
            finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation : ℝ) ^ 2) =
      (∑ U : FiniteEvenFourTorusZ2TemporalLinkField 0,
          (finiteEvenFourTorusZ2CrossingNontrivialCount 0 U
            finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity
            finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation : ℝ) ^ 2) +
        (∑ U : FiniteEvenFourTorusZ2TemporalLinkField 0,
          (finiteEvenFourTorusZ2CrossingNontrivialCount 0 U
            finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation
            finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity : ℝ) ^ 2) +
        2 * n := by
    simpa [n] using hsecond
  field_simp [hn]
  linear_combination
    (2 * m * energyIdentity * d) * hfirst' + d ^ 2 * hsecond'

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
