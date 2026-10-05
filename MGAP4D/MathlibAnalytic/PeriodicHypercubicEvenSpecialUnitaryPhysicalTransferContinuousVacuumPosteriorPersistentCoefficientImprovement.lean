import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorPersistentFixedVolumeStrictDobrushin
import MGAP4D.MathlibAnalytic.FinitePositiveWeightCrossRatioInfluenceTransform
import Mathlib.Tactic

/-!
# Persistent posterior coefficient improvement near zero coupling

PR #5186 closes one fixed-volume response -> refined influence -> strictness
bootstrap loop.  This file proves that, after shrinking to a still-positive
fixed-volume neighborhood of beta = 0, the persistent refined coefficient is
not merely strict: it is no larger than the original zero-depth
first-bootstrap coefficient.

The mechanism is elementary and quantitative.  If

  alpha_H^(1)(beta) <= 1/2,

then

  1 / (1 - alpha_H^(1)) <= 2.

Together with

  width(beta) <= exp(8 beta)

for beta >= 0, this gives

  epsilon_persistent(H,beta)
    <= epsilon_zeroDepth(H,beta).

The remote influence transform is monotone in its response radius, while the
local direct coefficient is unchanged.  Hence every persistent refined entry
is bounded by the corresponding zero-depth refined entry and therefore

  alpha_H^(2)(beta) <= alpha_H^(1)(beta).

A canonical positive cutoff inside the second strict interval is selected on
which alpha_H^(1) < 1/2, so alpha_H^(2) < 1/2 as well.

This is a fixed-volume sharpening theorem.  The cutoff remains H-dependent;
no volume-uniform strictness, spatial decay, Euclidean-time identification,
continuum generator bridge, H1-D5 exact descent, or complete Yang--Mills
mass-gap claim is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance posteriorPersistentCoefficientImprovementSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The response-radius to remote-influence transform is monotone in epsilon. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence_mono_epsilon
    (beta epsilon₁ epsilon₂ : ℝ)
    (hEpsilon : epsilon₁ ≤ epsilon₂) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence
        beta epsilon₁ ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence
        beta epsilon₂ := by
  let floor : ℝ := Real.exp (-8 * beta)
  have hFloor : 0 < floor := by
    dsimp [floor]
    positivity
  have hRatio :
      epsilon₁ / floor ≤ epsilon₂ / floor :=
    (div_le_div_iff_of_pos_right hFloor).2 hEpsilon
  have hRadius :
      2 * (epsilon₁ / floor) ≤ 2 * (epsilon₂ / floor) :=
    mul_le_mul_of_nonneg_left hRatio (by norm_num)
  have hTransform :=
    finitePositiveWeightCrossRatioInfluenceTransform_mono hRadius
  unfold finitePositiveWeightCrossRatioInfluenceTransform at hTransform
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence
  dsimp [floor] at hTransform ⊢
  nlinarith

/-- The exact one-slab target-local variation width is bounded by exp(8 beta)
at nonnegative coupling. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth_le_exp_eight
    (beta : ℝ) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
        beta ≤
      Real.exp (8 * beta) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
  have hExp : 0 ≤ Real.exp (-8 * beta) := (Real.exp_pos _).le
  linarith

/-- Once the first refined total coefficient is at most one half, the
terminal-free persistent response radius improves the zero-depth response
radius. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentResponseRadius_le_zeroDepthResponseRadius_of_totalCoefficient_le_half
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hAlphaHalf :
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient
          H beta ≤ (1 / 2 : ℝ)) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentResponseRadius
        H beta ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapResponseRadius
        H beta 0 := by
  let width :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
      beta
  let alpha :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient
      H beta
  let floor := Real.exp (-8 * beta)
  have hWidth : 0 ≤ width := by
    dsimp [width]
    exact
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth_nonneg
        beta hbeta
  have hWidthExp : width ≤ Real.exp (8 * beta) := by
    dsimp [width]
    exact
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth_le_exp_eight
        beta
  have hAlphaHalf' : alpha ≤ (1 / 2 : ℝ) := by
    simpa [alpha] using hAlphaHalf
  have hHalfDen : (1 / 2 : ℝ) ≤ 1 - alpha := by
    linarith
  have hDenPos : 0 < 1 - alpha :=
    lt_of_lt_of_le (by norm_num) hHalfDen
  have hRatio :
      width / (1 - alpha) ≤ 2 * width := by
    apply (div_le_iff₀ hDenPos).2
    have hMul :=
      mul_le_mul_of_nonneg_left hHalfDen hWidth
    nlinarith
  have hHalfRatio :
      (width / 2) * (width / (1 - alpha)) ≤ width * width := by
    calc
      (width / 2) * (width / (1 - alpha)) ≤
          (width / 2) * (2 * width) :=
        mul_le_mul_of_nonneg_left hRatio
          (div_nonneg hWidth (by norm_num))
      _ = width * width := by ring
  have hSquareExp :
      width * width ≤ Real.exp (8 * beta) * width :=
    mul_le_mul_of_nonneg_right hWidthExp hWidth
  have hNumerator :
      (width / 2) * (width / (1 - alpha)) ≤
        Real.exp (8 * beta) * width :=
    le_trans hHalfRatio hSquareExp
  have hFloorPos : 0 < floor := by
    dsimp [floor]
    positivity
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentResponseRadius
  rw [
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapResponseRadius_zeroDepth_eq]
  change
    ((width / 2) * (width / (1 - alpha))) / floor ≤
      (Real.exp (8 * beta) * width) / floor
  exact
    (div_le_div_iff_of_pos_right hFloorPos).2 hNumerator

/-- Under the same one-half hypothesis, every persistent refined influence
entry is bounded by the corresponding zero-depth refined entry. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedInfluence_le_zeroDepthRefinedInfluence_of_totalCoefficient_le_half
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hAlphaHalf :
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient
          H beta ≤ (1 / 2 : ℝ))
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedInfluence
        H beta target source ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedInfluence
        H beta target source := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedInfluence
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedInfluence
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence
  by_cases hdiag : source = target
  · simp [hdiag]
  · simp only [hdiag, if_false]
    by_cases hlocal :
        periodicHypercubicEvenSpatialSlicePlaquetteLocal H target source
    · simp [hlocal]
    · simp only [hlocal, if_false]
      exact
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence_mono_epsilon
          beta
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentResponseRadius
            H beta)
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapResponseRadius
            H beta 0)
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentResponseRadius_le_zeroDepthResponseRadius_of_totalCoefficient_le_half
            H beta hbeta hAlphaHalf)

/-- Therefore the complete persistent refined total coefficient is no larger
than the original zero-depth first-bootstrap coefficient whenever the latter is
at most one half. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedTotalCoefficient_le_zeroDepthRefinedTotalCoefficient_of_le_half
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hAlphaHalf :
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient
          H beta ≤ (1 / 2 : ℝ)) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedTotalCoefficient
        H beta ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient
        H beta := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedTotalCoefficient
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient
  apply Finset.sum_le_sum
  intro target _hTarget
  apply Finset.sum_le_sum
  intro source _hSource
  exact
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedInfluence_le_zeroDepthRefinedInfluence_of_totalCoefficient_le_half
      H beta hbeta hAlphaHalf target source

/-- There is a positive fixed-volume interval inside the second strict cutoff
on which the first coefficient is already below one half. -/
theorem
    exists_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentCoefficientImprovementCutoff
    (H : ℕ) :
    ∃ cutoff : ℝ,
      0 < cutoff ∧
      cutoff <
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinCutoff
          H ∧
      ∀ beta : ℝ, 0 < beta → beta < cutoff →
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient
            H beta < (1 / 2 : ℝ) := by
  let alpha : ℝ → ℝ := fun beta =>
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient
      H beta
  have hAt : ContinuousAt alpha 0 := by
    dsimp [alpha]
    exact
      (continuous_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient
        H).continuousAt
  rw [Metric.continuousAt_iff] at hAt
  obtain ⟨delta, hDelta, hControl⟩ :=
    hAt (1 / 2) (by norm_num)
  let secondCutoff :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinCutoff
      H
  have hSecondPos : 0 < secondCutoff := by
    dsimp [secondCutoff]
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinCutoff_pos
        H
  let cutoff := min (delta / 2) (secondCutoff / 2)
  refine ⟨cutoff, ?_, ?_, ?_⟩
  · dsimp [cutoff]
    exact lt_min (by positivity) (by positivity)
  · dsimp [cutoff]
    calc
      min (delta / 2) (secondCutoff / 2) ≤ secondCutoff / 2 :=
        min_le_right _ _
      _ < secondCutoff := by linarith
  · intro beta hbeta hbetaCutoff
    have hBetaDelta : beta < delta := by
      have hBetaLocal :
          beta < delta / 2 :=
        lt_of_lt_of_le hbetaCutoff
          (by
            dsimp [cutoff]
            exact min_le_left _ _)
      linarith
    have hDist : dist beta 0 < delta := by
      rw [Real.dist_eq]
      simp [abs_of_pos hbeta]
      exact hBetaDelta
    have hImage := hControl hDist
    have hAlphaZero : alpha 0 = 0 := by
      dsimp [alpha]
      exact
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient_zero
          H
    rw [hAlphaZero] at hImage
    have hAbs : |alpha beta| < (1 / 2 : ℝ) := by
      simpa [Real.dist_eq] using hImage
    exact lt_of_le_of_lt (le_abs_self (alpha beta)) hAbs

/-- Canonically selected fixed-volume coefficient-improvement cutoff. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentCoefficientImprovementCutoff
    (H : ℕ) : ℝ :=
  Classical.choose
    (exists_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentCoefficientImprovementCutoff
      H)

theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentCoefficientImprovementCutoff_pos
    (H : ℕ) :
    0 <
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentCoefficientImprovementCutoff
        H :=
  (Classical.choose_spec
    (exists_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentCoefficientImprovementCutoff
      H)).1

theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentCoefficientImprovementCutoff_lt_secondCutoff
    (H : ℕ) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentCoefficientImprovementCutoff
        H <
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinCutoff
        H :=
  (Classical.choose_spec
    (exists_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentCoefficientImprovementCutoff
      H)).2.1

theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentCoefficientImprovementCutoff_firstCoefficient_lt_half
    (H : ℕ)
    (beta : ℝ)
    (hbetaPos : 0 < beta)
    (hbetaCutoff :
      beta <
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentCoefficientImprovementCutoff
          H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient
        H beta < (1 / 2 : ℝ) :=
  (Classical.choose_spec
    (exists_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentCoefficientImprovementCutoff
      H)).2.2
    beta hbetaPos hbetaCutoff

/-- On the canonical improvement interval, the persistent second coefficient is
no larger than the first coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentCoefficientImprovementCutoff_secondCoefficient_le_firstCoefficient
    (H : ℕ)
    (beta : ℝ)
    (hbetaPos : 0 < beta)
    (hbetaCutoff :
      beta <
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentCoefficientImprovementCutoff
          H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedTotalCoefficient
        H beta ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient
        H beta := by
  have hFirstHalf :
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient
          H beta < (1 / 2 : ℝ) :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentCoefficientImprovementCutoff_firstCoefficient_lt_half
      H beta hbetaPos hbetaCutoff
  exact
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedTotalCoefficient_le_zeroDepthRefinedTotalCoefficient_of_le_half
      H beta hbetaPos.le hFirstHalf.le

/-- In particular, the persistent second coefficient is itself below one half
on the improvement interval. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentCoefficientImprovementCutoff_secondCoefficient_lt_half
    (H : ℕ)
    (beta : ℝ)
    (hbetaPos : 0 < beta)
    (hbetaCutoff :
      beta <
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentCoefficientImprovementCutoff
          H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedTotalCoefficient
        H beta < (1 / 2 : ℝ) := by
  exact
    lt_of_le_of_lt
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentCoefficientImprovementCutoff_secondCoefficient_le_firstCoefficient
        H beta hbetaPos hbetaCutoff)
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentCoefficientImprovementCutoff_firstCoefficient_lt_half
        H beta hbetaPos hbetaCutoff)

end

end MathlibAnalytic
end MGAP4D
