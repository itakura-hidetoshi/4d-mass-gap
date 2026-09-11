import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobAugmentedPosteriorCommonMassCoupling
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The lower-slice projection of the explicit augmented common-mass coupling.
The two temporal-link fields are summed out, leaving a coupling of the actual
lower-boundary Doob output laws. -/
def finiteEvenFourTorusZ2UnfixedGaugeDoobCommonMassLowerCoupling
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (source : FiniteEvenFourTorusSpatialLink H)
    (A B X Y : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedCouplingLowerMarginal
    H
    (finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedCommonMassCoupling
      H β energyIdentity energyNontrivial hβ hEnergy)
    source A B X Y

/-- The projected common-mass coupling is nonnegative whenever the two upper
boundaries agree away from the declared source link. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobCommonMassLowerCoupling_nonneg
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (source : FiniteEvenFourTorusSpatialLink H)
    (A B X Y : FiniteEvenFourTorusZ2SliceConfiguration H)
    (hAgree : FiniteProductAgreeOff A B source) :
    0 ≤ finiteEvenFourTorusZ2UnfixedGaugeDoobCommonMassLowerCoupling
      H β energyIdentity energyNontrivial hβ hEnergy source A B X Y := by
  classical
  unfold finiteEvenFourTorusZ2UnfixedGaugeDoobCommonMassLowerCoupling
  unfold finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedCouplingLowerMarginal
  apply Finset.sum_nonneg
  intro U _hU
  apply Finset.sum_nonneg
  intro V _hV
  exact
    finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedCommonMassCoupling_nonneg
      H β energyIdentity energyNontrivial hβ hEnergy source A B hAgree U X V Y

/-- The left marginal of the projected coupling is the actual Perron-ground
Doob output law at upper boundary `A`. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobCommonMassLowerCoupling_leftMarginal
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (source : FiniteEvenFourTorusSpatialLink H)
    (A B X : FiniteEvenFourTorusZ2SliceConfiguration H) :
    (∑ Y : FiniteEvenFourTorusZ2SliceConfiguration H,
      finiteEvenFourTorusZ2UnfixedGaugeDoobCommonMassLowerCoupling
        H β energyIdentity energyNontrivial hβ hEnergy source A B X Y) =
      finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel
        H β energyIdentity energyNontrivial hβ hEnergy X A := by
  classical
  unfold finiteEvenFourTorusZ2UnfixedGaugeDoobCommonMassLowerCoupling
  unfold finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedCouplingLowerMarginal
  calc
    (∑ Y : FiniteEvenFourTorusZ2SliceConfiguration H,
      ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
        ∑ V : FiniteEvenFourTorusZ2TemporalLinkField H,
          finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedCommonMassCoupling
            H β energyIdentity energyNontrivial hβ hEnergy
            source A B U X V Y) =
        ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
          ∑ Y : FiniteEvenFourTorusZ2SliceConfiguration H,
            ∑ V : FiniteEvenFourTorusZ2TemporalLinkField H,
              finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedCommonMassCoupling
                H β energyIdentity energyNontrivial hβ hEnergy
                source A B U X V Y := by
      rw [Finset.sum_comm]
    _ = ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
          ∑ V : FiniteEvenFourTorusZ2TemporalLinkField H,
            ∑ Y : FiniteEvenFourTorusZ2SliceConfiguration H,
              finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedCommonMassCoupling
                H β energyIdentity energyNontrivial hβ hEnergy
                source A B U X V Y := by
      apply Finset.sum_congr rfl
      intro U _hU
      rw [Finset.sum_comm]
    _ = ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
          finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior
            H β energyIdentity energyNontrivial hβ hEnergy U X A := by
      apply Finset.sum_congr rfl
      intro U _hU
      exact
        finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedCommonMassCoupling_leftMarginal
          H β energyIdentity energyNontrivial hβ hEnergy source A B U X
    _ = finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel
          H β energyIdentity energyNontrivial hβ hEnergy X A :=
      finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior_sum_temporal
        H β energyIdentity energyNontrivial hβ hEnergy X A

/-- The right marginal of the projected coupling is the actual Perron-ground
Doob output law at upper boundary `B`. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobCommonMassLowerCoupling_rightMarginal
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (source : FiniteEvenFourTorusSpatialLink H)
    (A B Y : FiniteEvenFourTorusZ2SliceConfiguration H) :
    (∑ X : FiniteEvenFourTorusZ2SliceConfiguration H,
      finiteEvenFourTorusZ2UnfixedGaugeDoobCommonMassLowerCoupling
        H β energyIdentity energyNontrivial hβ hEnergy source A B X Y) =
      finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel
        H β energyIdentity energyNontrivial hβ hEnergy Y B := by
  classical
  unfold finiteEvenFourTorusZ2UnfixedGaugeDoobCommonMassLowerCoupling
  unfold finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedCouplingLowerMarginal
  calc
    (∑ X : FiniteEvenFourTorusZ2SliceConfiguration H,
      ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
        ∑ V : FiniteEvenFourTorusZ2TemporalLinkField H,
          finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedCommonMassCoupling
            H β energyIdentity energyNontrivial hβ hEnergy
            source A B U X V Y) =
        ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
          ∑ X : FiniteEvenFourTorusZ2SliceConfiguration H,
            ∑ V : FiniteEvenFourTorusZ2TemporalLinkField H,
              finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedCommonMassCoupling
                H β energyIdentity energyNontrivial hβ hEnergy
                source A B U X V Y := by
      rw [Finset.sum_comm]
    _ = ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
          ∑ V : FiniteEvenFourTorusZ2TemporalLinkField H,
            ∑ X : FiniteEvenFourTorusZ2SliceConfiguration H,
              finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedCommonMassCoupling
                H β energyIdentity energyNontrivial hβ hEnergy
                source A B U X V Y := by
      apply Finset.sum_congr rfl
      intro U _hU
      rw [Finset.sum_comm]
    _ = ∑ V : FiniteEvenFourTorusZ2TemporalLinkField H,
          ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
            ∑ X : FiniteEvenFourTorusZ2SliceConfiguration H,
              finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedCommonMassCoupling
                H β energyIdentity energyNontrivial hβ hEnergy
                source A B U X V Y := by
      rw [Finset.sum_comm]
    _ = ∑ V : FiniteEvenFourTorusZ2TemporalLinkField H,
          finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior
            H β energyIdentity energyNontrivial hβ hEnergy V Y B := by
      apply Finset.sum_congr rfl
      intro V _hV
      exact
        finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedCommonMassCoupling_rightMarginal
          H β energyIdentity energyNontrivial hβ hEnergy source A B V Y
    _ = finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel
          H β energyIdentity energyNontrivial hβ hEnergy Y B :=
      finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior_sum_temporal
        H β energyIdentity energyNontrivial hβ hEnergy Y B

/-- Temporal-link marginalization preserves the explicit common-mass lower
coordinate mismatch estimate exactly. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobCommonMassLowerCoupling_mismatch_le
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (source target : FiniteEvenFourTorusSpatialLink H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (hAgree : FiniteProductAgreeOff A B source) :
    (∑ X : FiniteEvenFourTorusZ2SliceConfiguration H,
      ∑ Y : FiniteEvenFourTorusZ2SliceConfiguration H,
        finiteEvenFourTorusZ2UnfixedGaugeDoobCommonMassLowerCoupling
            H β energyIdentity energyNontrivial hβ hEnergy source A B X Y *
          finiteProductMismatchIndicator X Y target) ≤
      1 - (z2UnfixedGaugeDoobAugmentedStateSourceRatio
        β energyIdentity energyNontrivial)⁻¹ := by
  classical
  unfold finiteEvenFourTorusZ2UnfixedGaugeDoobCommonMassLowerCoupling
  unfold finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedCouplingLowerMarginal
  simp_rw [Finset.sum_mul]
  calc
    (∑ X : FiniteEvenFourTorusZ2SliceConfiguration H,
      ∑ Y : FiniteEvenFourTorusZ2SliceConfiguration H,
        ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
          ∑ V : FiniteEvenFourTorusZ2TemporalLinkField H,
            finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedCommonMassCoupling
                H β energyIdentity energyNontrivial hβ hEnergy
                source A B U X V Y *
              finiteProductMismatchIndicator X Y target) =
        ∑ X : FiniteEvenFourTorusZ2SliceConfiguration H,
          ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
            ∑ Y : FiniteEvenFourTorusZ2SliceConfiguration H,
              ∑ V : FiniteEvenFourTorusZ2TemporalLinkField H,
                finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedCommonMassCoupling
                    H β energyIdentity energyNontrivial hβ hEnergy
                    source A B U X V Y *
                  finiteProductMismatchIndicator X Y target := by
      apply Finset.sum_congr rfl
      intro X _hX
      rw [Finset.sum_comm]
    _ = ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
          ∑ X : FiniteEvenFourTorusZ2SliceConfiguration H,
            ∑ Y : FiniteEvenFourTorusZ2SliceConfiguration H,
              ∑ V : FiniteEvenFourTorusZ2TemporalLinkField H,
                finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedCommonMassCoupling
                    H β energyIdentity energyNontrivial hβ hEnergy
                    source A B U X V Y *
                  finiteProductMismatchIndicator X Y target := by
      rw [Finset.sum_comm]
    _ = ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
          ∑ X : FiniteEvenFourTorusZ2SliceConfiguration H,
            ∑ V : FiniteEvenFourTorusZ2TemporalLinkField H,
              ∑ Y : FiniteEvenFourTorusZ2SliceConfiguration H,
                finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedCommonMassCoupling
                    H β energyIdentity energyNontrivial hβ hEnergy
                    source A B U X V Y *
                  finiteProductMismatchIndicator X Y target := by
      apply Finset.sum_congr rfl
      intro U _hU
      apply Finset.sum_congr rfl
      intro X _hX
      rw [Finset.sum_comm]
    _ ≤ 1 - (z2UnfixedGaugeDoobAugmentedStateSourceRatio
          β energyIdentity energyNontrivial)⁻¹ :=
      finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedCommonMassCoupling_mismatch_le
        H β energyIdentity energyNontrivial hβ hEnergy
        source target A B hAgree

/-- The inverse source ratio is the expected explicit exponential residual
mass factor. -/
theorem z2UnfixedGaugeDoobAugmentedStateSourceRatio_inv_eq_exp_neg_fourteen
    (β energyIdentity energyNontrivial : ℝ) :
    (z2UnfixedGaugeDoobAugmentedStateSourceRatio
      β energyIdentity energyNontrivial)⁻¹ =
      Real.exp
        (-14 * β * (energyNontrivial - energyIdentity)) := by
  unfold z2UnfixedGaugeDoobAugmentedStateSourceRatio
  unfold z2UnfixedGaugeDoobAugmentedBoundaryRatio
  calc
    ((Real.exp (7 * β * (energyNontrivial - energyIdentity))) ^ 2)⁻¹ =
        ((Real.exp (7 * β * (energyNontrivial - energyIdentity)))⁻¹) ^ 2 := by
      rw [inv_pow]
    _ = (Real.exp (-(7 * β * (energyNontrivial - energyIdentity)))) ^ 2 := by
      rw [← Real.exp_neg]
    _ = Real.exp
          (-(7 * β * (energyNontrivial - energyIdentity)) +
            -(7 * β * (energyNontrivial - energyIdentity))) := by
      rw [pow_two, ← Real.exp_add]
    _ = Real.exp
          (-14 * β * (energyNontrivial - energyIdentity)) := by
      congr 1
      ring

/-- Explicit finite-volume baseline: the actual lower-slice Doob output
coupling has the correct marginals and every coordinate mismatch is bounded by
`1 - exp(-14 * beta * DeltaE)`.  This is a global bound and is not a uniform
strict column-sum certificate. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobCommonMassLowerCoupling_mismatch_le_exp
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (source target : FiniteEvenFourTorusSpatialLink H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (hAgree : FiniteProductAgreeOff A B source) :
    (∑ X : FiniteEvenFourTorusZ2SliceConfiguration H,
      ∑ Y : FiniteEvenFourTorusZ2SliceConfiguration H,
        finiteEvenFourTorusZ2UnfixedGaugeDoobCommonMassLowerCoupling
            H β energyIdentity energyNontrivial hβ hEnergy source A B X Y *
          finiteProductMismatchIndicator X Y target) ≤
      1 - Real.exp
        (-14 * β * (energyNontrivial - energyIdentity)) := by
  rw [← z2UnfixedGaugeDoobAugmentedStateSourceRatio_inv_eq_exp_neg_fourteen]
  exact
    finiteEvenFourTorusZ2UnfixedGaugeDoobCommonMassLowerCoupling_mismatch_le
      H β energyIdentity energyNontrivial hβ hEnergy
      source target A B hAgree

end

end MathlibAnalytic
end MGAP4D
