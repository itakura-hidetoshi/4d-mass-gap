import MGAP4D.MathlibAnalytic.FiniteProbabilityLikelihoodRatioCoupling
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobAugmentedCouplingMarginal
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobAugmentedPosteriorBoundaryRatio
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The finite augmented one-slab state consists of a temporal-link field and
a lower boundary slice. -/
abbrev Z2UnfixedGaugeDoobAugmentedState (H : ℕ) :=
  FiniteEvenFourTorusZ2TemporalLinkField H ×
    FiniteEvenFourTorusZ2SliceConfiguration H

/-- The normalized augmented posterior viewed as a probability weight on the
finite product state `(U,A)`. -/
def finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedStateWeight
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (s : Z2UnfixedGaugeDoobAugmentedState H) : ℝ :=
  finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior
    H β energyIdentity energyNontrivial hβ hEnergy s.1 s.2 B

/-- The augmented state weight is nonnegative. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedStateWeight_nonneg
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (s : Z2UnfixedGaugeDoobAugmentedState H) :
    0 ≤ finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedStateWeight
      H β energyIdentity energyNontrivial hβ hEnergy B s := by
  exact
    finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior_nonneg
      H β energyIdentity energyNontrivial hβ hEnergy s.1 s.2 B

/-- The augmented state weight has total mass one. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedStateWeight_sum_eq_one
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    (∑ s : Z2UnfixedGaugeDoobAugmentedState H,
      finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedStateWeight
        H β energyIdentity energyNontrivial hβ hEnergy B s) = 1 := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  exact
    finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior_sum_eq_one
      H β energyIdentity energyNontrivial hβ hEnergy B

/-- The normalized one-source likelihood-ratio factor on augmented states. -/
def z2UnfixedGaugeDoobAugmentedStateSourceRatio
    (β energyIdentity energyNontrivial : ℝ) : ℝ :=
  (z2UnfixedGaugeDoobAugmentedBoundaryRatio
    β energyIdentity energyNontrivial) ^ 2

/-- The augmented state source ratio is strictly positive. -/
theorem z2UnfixedGaugeDoobAugmentedStateSourceRatio_pos
    (β energyIdentity energyNontrivial : ℝ) :
    0 < z2UnfixedGaugeDoobAugmentedStateSourceRatio
      β energyIdentity energyNontrivial := by
  exact pow_pos
    (z2UnfixedGaugeDoobAugmentedBoundaryRatio_pos
      β energyIdentity energyNontrivial) 2

/-- The source ratio is at least one in the physical high-temperature
parameter sector. -/
theorem one_le_z2UnfixedGaugeDoobAugmentedStateSourceRatio
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    1 ≤ z2UnfixedGaugeDoobAugmentedStateSourceRatio
      β energyIdentity energyNontrivial := by
  have hExponent :
      0 ≤ 7 * β * (energyNontrivial - energyIdentity) := by
    positivity
  have hBase :
      1 ≤ z2UnfixedGaugeDoobAugmentedBoundaryRatio
        β energyIdentity energyNontrivial := by
    unfold z2UnfixedGaugeDoobAugmentedBoundaryRatio
    exact Real.one_le_exp.mpr hExponent
  unfold z2UnfixedGaugeDoobAugmentedStateSourceRatio
  nlinarith [sq_nonneg
    (z2UnfixedGaugeDoobAugmentedBoundaryRatio
      β energyIdentity energyNontrivial - 1)]

/-- Upper boundaries agreeing away from one source link satisfy the same
pointwise augmented-state likelihood-ratio bound proved for an explicit
coordinate replacement. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedStateWeight_le_sourceRatio_mul_of_agreeOff
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (source : FiniteEvenFourTorusSpatialLink H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (hAgree : FiniteProductAgreeOff A B source)
    (s : Z2UnfixedGaugeDoobAugmentedState H) :
    finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedStateWeight
        H β energyIdentity energyNontrivial hβ hEnergy A s ≤
      z2UnfixedGaugeDoobAugmentedStateSourceRatio
          β energyIdentity energyNontrivial *
        finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedStateWeight
          H β energyIdentity energyNontrivial hβ hEnergy B s := by
  have hReplace :
      finiteZ2GaugeReplaceCoordinate A source (B source) = B := by
    simpa [finiteZ2GaugeReplaceCoordinate] using
      finiteProductUpdate_right_of_agreeOff A B source hAgree
  simpa [finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedStateWeight,
    z2UnfixedGaugeDoobAugmentedStateSourceRatio, hReplace] using
      finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior_le_boundaryRatio_sq_mul_replace
        H β energyIdentity energyNontrivial hβ hEnergy
        s.1 s.2 A source (B source)

/-- The explicit common-mass coupling of the two augmented posterior state
weights. -/
def finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedStateCommonMassCoupling
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (s t : Z2UnfixedGaugeDoobAugmentedState H) : ℝ :=
  finiteProbabilityLikelihoodRatioCoupling
    (finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedStateWeight
      H β energyIdentity energyNontrivial hβ hEnergy A)
    (finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedStateWeight
      H β energyIdentity energyNontrivial hβ hEnergy B)
    (z2UnfixedGaugeDoobAugmentedStateSourceRatio
      β energyIdentity energyNontrivial)
    s t

/-- Expanded form of the common-mass coupling on temporal-link fields and
lower boundary slices. -/
def finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedCommonMassCoupling
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (_source : FiniteEvenFourTorusSpatialLink H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (X : FiniteEvenFourTorusZ2SliceConfiguration H)
    (V : FiniteEvenFourTorusZ2TemporalLinkField H)
    (Y : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedStateCommonMassCoupling
    H β energyIdentity energyNontrivial hβ hEnergy A B (U, X) (V, Y)

/-- Under a one-source boundary relation, the actual augmented common-mass
coupling is nonnegative. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedCommonMassCoupling_nonneg
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (source : FiniteEvenFourTorusSpatialLink H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (hAgree : FiniteProductAgreeOff A B source)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (X : FiniteEvenFourTorusZ2SliceConfiguration H)
    (V : FiniteEvenFourTorusZ2TemporalLinkField H)
    (Y : FiniteEvenFourTorusZ2SliceConfiguration H) :
    0 ≤ finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedCommonMassCoupling
      H β energyIdentity energyNontrivial hβ hEnergy source A B U X V Y := by
  apply finiteProbabilityLikelihoodRatioCoupling_nonneg
  · intro s
    exact
      finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedStateWeight_nonneg
        H β energyIdentity energyNontrivial hβ hEnergy A s
  · exact z2UnfixedGaugeDoobAugmentedStateSourceRatio_pos
      β energyIdentity energyNontrivial
  · intro s
    exact
      finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedStateWeight_le_sourceRatio_mul_of_agreeOff
        H β energyIdentity energyNontrivial hβ hEnergy source A B hAgree s

/-- The first augmented posterior is the left marginal of the common-mass
coupling. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedCommonMassCoupling_leftMarginal
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (source : FiniteEvenFourTorusSpatialLink H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (X : FiniteEvenFourTorusZ2SliceConfiguration H) :
    (∑ V : FiniteEvenFourTorusZ2TemporalLinkField H,
      ∑ Y : FiniteEvenFourTorusZ2SliceConfiguration H,
        finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedCommonMassCoupling
          H β energyIdentity energyNontrivial hβ hEnergy source A B U X V Y) =
      finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior
        H β energyIdentity energyNontrivial hβ hEnergy U X A := by
  rw [← Fintype.sum_prod_type]
  exact
    finiteProbabilityLikelihoodRatioCoupling_leftMarginal
      (finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedStateWeight
        H β energyIdentity energyNontrivial hβ hEnergy A)
      (finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedStateWeight
        H β energyIdentity energyNontrivial hβ hEnergy B)
      (z2UnfixedGaugeDoobAugmentedStateSourceRatio
        β energyIdentity energyNontrivial)
      (finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedStateWeight_sum_eq_one
        H β energyIdentity energyNontrivial hβ hEnergy A)
      (finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedStateWeight_sum_eq_one
        H β energyIdentity energyNontrivial hβ hEnergy B)
      (U, X)

/-- The second augmented posterior is the right marginal of the common-mass
coupling. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedCommonMassCoupling_rightMarginal
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (source : FiniteEvenFourTorusSpatialLink H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (V : FiniteEvenFourTorusZ2TemporalLinkField H)
    (Y : FiniteEvenFourTorusZ2SliceConfiguration H) :
    (∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
      ∑ X : FiniteEvenFourTorusZ2SliceConfiguration H,
        finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedCommonMassCoupling
          H β energyIdentity energyNontrivial hβ hEnergy source A B U X V Y) =
      finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior
        H β energyIdentity energyNontrivial hβ hEnergy V Y B := by
  rw [← Fintype.sum_prod_type]
  exact
    finiteProbabilityLikelihoodRatioCoupling_rightMarginal
      (finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedStateWeight
        H β energyIdentity energyNontrivial hβ hEnergy A)
      (finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedStateWeight
        H β energyIdentity energyNontrivial hβ hEnergy B)
      (z2UnfixedGaugeDoobAugmentedStateSourceRatio
        β energyIdentity energyNontrivial)
      (finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedStateWeight_sum_eq_one
        H β energyIdentity energyNontrivial hβ hEnergy A)
      (V, Y)

/-- Every lower-slice coordinate mismatch under the common-mass coupling is
bounded by the same global residual mass `1 - R_aug⁻²`. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedCommonMassCoupling_mismatch_le
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (source target : FiniteEvenFourTorusSpatialLink H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (hAgree : FiniteProductAgreeOff A B source) :
    (∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
      ∑ X : FiniteEvenFourTorusZ2SliceConfiguration H,
        ∑ V : FiniteEvenFourTorusZ2TemporalLinkField H,
          ∑ Y : FiniteEvenFourTorusZ2SliceConfiguration H,
            finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedCommonMassCoupling
                H β energyIdentity energyNontrivial hβ hEnergy
                source A B U X V Y *
              finiteProductMismatchIndicator X Y target) ≤
      1 - (z2UnfixedGaugeDoobAugmentedStateSourceRatio
        β energyIdentity energyNontrivial)⁻¹ := by
  let μ := finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedStateWeight
    H β energyIdentity energyNontrivial hβ hEnergy A
  let ν := finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedStateWeight
    H β energyIdentity energyNontrivial hβ hEnergy B
  let R := z2UnfixedGaugeDoobAugmentedStateSourceRatio
    β energyIdentity energyNontrivial
  have hCost :=
    finiteProbabilityLikelihoodRatioCoupling_cost_le_one_sub_inv
      μ ν R
      (fun s =>
        finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedStateWeight_nonneg
          H β energyIdentity energyNontrivial hβ hEnergy A s)
      (finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedStateWeight_sum_eq_one
        H β energyIdentity energyNontrivial hβ hEnergy A)
      (finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedStateWeight_sum_eq_one
        H β energyIdentity energyNontrivial hβ hEnergy B)
      (z2UnfixedGaugeDoobAugmentedStateSourceRatio_pos
        β energyIdentity energyNontrivial)
      (fun s =>
        finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedStateWeight_le_sourceRatio_mul_of_agreeOff
          H β energyIdentity energyNontrivial hβ hEnergy source A B hAgree s)
      (fun s t => finiteProductMismatchIndicator s.2 t.2 target)
      (fun s t => finiteProductMismatchIndicator_nonneg s.2 t.2 target)
      (by
        intro s t
        unfold finiteProductMismatchIndicator
        split <;> norm_num)
      (by
        intro s
        simp [finiteProductMismatchIndicator])
  simpa [μ, ν, R,
    finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedStateCommonMassCoupling,
    finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedCommonMassCoupling,
    Fintype.sum_prod_type] using hCost

/-- The global residual disagreement coefficient is nonnegative in the
physical parameter sector. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedCommonMassResidual_nonneg
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    0 ≤ 1 - (z2UnfixedGaugeDoobAugmentedStateSourceRatio
      β energyIdentity energyNontrivial)⁻¹ :=
  one_sub_inv_nonneg_of_one_le
    (z2UnfixedGaugeDoobAugmentedStateSourceRatio
      β energyIdentity energyNontrivial)
    (one_le_z2UnfixedGaugeDoobAugmentedStateSourceRatio
      β energyIdentity energyNontrivial hβ hEnergy)

end

end MathlibAnalytic
end MGAP4D
