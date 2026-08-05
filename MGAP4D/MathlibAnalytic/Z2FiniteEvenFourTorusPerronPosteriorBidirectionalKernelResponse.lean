import MGAP4D.MathlibAnalytic.FinitePositiveWeightBidirectionalInfluenceKernelResponse
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorNonstrictKernelResponse
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The target-tilt envelope amplitude is nonnegative. -/
theorem finiteEvenFourTorusZ2PerronPosteriorTargetTiltSourceAmplitude_nonneg
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    0 ≤ finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTiltSourceAmplitude
      β energyIdentity energyNontrivial := by
  let ratio := finiteZ2CrossingLikelihoodRatio
    (z2WilsonTemporalCrossingRate
      β energyIdentity energyNontrivial)
  have hRatioPos : 0 < ratio :=
    finiteZ2CrossingLikelihoodRatio_pos
      (z2WilsonTemporalCrossingRate_pos hβ hEnergy).le
      (z2WilsonTemporalCrossingRate_lt_one hβ hEnergy)
  have hRatioOne : 1 ≤ ratio :=
    one_le_finiteZ2CrossingLikelihoodRatio
      (z2WilsonTemporalCrossingRate_pos hβ hEnergy).le
      (z2WilsonTemporalCrossingRate_lt_one hβ hEnergy)
  have hInvLeOne : ratio⁻¹ ≤ 1 :=
    (inv_le_one₀ hRatioPos).2 hRatioOne
  have hLowerUpper : ratio⁻¹ ≤ ratio :=
    le_trans hInvLeOne hRatioOne
  have hQuotientOne : 1 ≤ ratio / ratio⁻¹ := by
    exact (le_div_iff₀ (inv_pos.mpr hRatioPos)).2
      (by simpa using hLowerUpper)
  have hQuotientPos : 0 < ratio / ratio⁻¹ :=
    div_pos hRatioPos (inv_pos.mpr hRatioPos)
  have hInverseLeOne : (ratio / ratio⁻¹)⁻¹ ≤ 1 :=
    (inv_le_one₀ hQuotientPos).2 hQuotientOne
  unfold
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTiltSourceAmplitude
  change 0 ≤ 2 * (1 - (ratio / ratio⁻¹)⁻¹)
  nlinarith

/-- The actual target-tilt source envelope is exactly a singleton profile. -/
theorem finiteEvenFourTorusZ2PerronPosteriorTargetTiltSourceEnvelope_eq_singleton
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (target : FiniteEvenFourTorusSpatialLink H) :
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTiltSourceEnvelope
        H β energyIdentity energyNontrivial target =
      finiteInfluenceKernelSingletonVariation
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTiltSourceAmplitude
          β energyIdentity energyNontrivial)
        target := by
  funext coordinate
  by_cases hEq : coordinate = target
  · subst coordinate
    simp [
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTiltSourceEnvelope,
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTiltSourceAmplitude,
      finitePositiveWeightLocalTiltConditionalSourceBound,
      finiteInfluenceKernelSingletonVariation]
  · simp [
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTiltSourceEnvelope,
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTiltSourceAmplitude,
      finitePositiveWeightLocalTiltConditionalSourceBound,
      finiteInfluenceKernelSingletonVariation,
      hEq]

/-- Finite non-strict response coefficient shared by actual response rows and
columns. -/
noncomputable def finiteEvenFourTorusZ2PerronPosteriorKernelFiniteResponseCoefficient
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (iterations : ℕ)
    (coefficient : ℝ) : ℝ :=
  let sourceMagnitude :=
    finiteZ2CrossingLikelihoodRatio
        (z2WilsonTemporalCrossingRate
          β energyIdentity energyNontrivial) -
      (finiteZ2CrossingLikelihoodRatio
        (z2WilsonTemporalCrossingRate
          β energyIdentity energyNontrivial))⁻¹
  finiteInfluenceKernelBidirectionalFiniteResponseCoefficient
    (FiniteEvenFourTorusSpatialLink H)
    iterations coefficient
    (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTiltSourceAmplitude
      β energyIdentity energyNontrivial)
    sourceMagnitude

/-- The actual finite response coefficient is nonnegative. -/
theorem finiteEvenFourTorusZ2PerronPosteriorKernelFiniteResponseCoefficient_nonneg
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (iterations : ℕ)
    (coefficient : ℝ)
    (hCoefficient : 0 ≤ coefficient) :
    0 ≤ finiteEvenFourTorusZ2PerronPosteriorKernelFiniteResponseCoefficient
      H β energyIdentity energyNontrivial iterations coefficient := by
  have hCard :
      0 < Fintype.card (FiniteEvenFourTorusSpatialLink H) :=
    Fintype.card_pos_iff.mpr
      ⟨(⟨0, by simp⟩, ⟨1, by norm_num⟩)⟩
  exact
    finiteInfluenceKernelBidirectionalFiniteResponseCoefficient_nonneg
      hCard iterations coefficient
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTiltSourceAmplitude
        β energyIdentity energyNontrivial)
      (finiteZ2CrossingLikelihoodRatio
          (z2WilsonTemporalCrossingRate
            β energyIdentity energyNontrivial) -
        (finiteZ2CrossingLikelihoodRatio
          (z2WilsonTemporalCrossingRate
            β energyIdentity energyNontrivial))⁻¹)
      hCoefficient
      (finiteEvenFourTorusZ2PerronPosteriorTargetTiltSourceAmplitude_nonneg
        β energyIdentity energyNontrivial hβ hEnergy)
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedSourceTiltAmplitude_nonneg
        β energyIdentity energyNontrivial hβ hEnergy)

/-- Source-summed finite response controlled by a column coefficient, without
assuming that coefficient is strict. -/
theorem finiteEvenFourTorusZ2PerronPosteriorKernelResponseErrorRowSum_le
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (kernel :
      FiniteNonnegativeInfluenceKernelData
        (FiniteEvenFourTorusSpatialLink H))
    (iterations : ℕ)
    (columnCoefficient : ℝ)
    (hColumnNonneg : 0 ≤ columnCoefficient)
    (hColumnSum :
      ∀ source : FiniteEvenFourTorusSpatialLink H,
        finiteInfluenceKernelColumnSum kernel source ≤ columnCoefficient)
    (target : FiniteEvenFourTorusSpatialLink H) :
    (∑ source : FiniteEvenFourTorusSpatialLink H,
      finiteEvenFourTorusZ2PerronPosteriorKernelResponseError
        H β energyIdentity energyNontrivial
        kernel iterations target source) ≤
      finiteEvenFourTorusZ2PerronPosteriorKernelFiniteResponseCoefficient
        H β energyIdentity energyNontrivial iterations columnCoefficient := by
  let sourceMagnitude :=
    finiteZ2CrossingLikelihoodRatio
        (z2WilsonTemporalCrossingRate
          β energyIdentity energyNontrivial) -
      (finiteZ2CrossingLikelihoodRatio
        (z2WilsonTemporalCrossingRate
          β energyIdentity energyNontrivial))⁻¹
  have hMagnitude : 0 ≤ sourceMagnitude :=
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedSourceTiltAmplitude_nonneg
      β energyIdentity energyNontrivial hβ hEnergy
  have hCard :
      0 < Fintype.card (FiniteEvenFourTorusSpatialLink H) :=
    Fintype.card_pos_iff.mpr ⟨target⟩
  have hEnvelopeNonneg :
      ∀ e : FiniteEvenFourTorusSpatialLink H,
        0 ≤ finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTiltSourceEnvelope
          H β energyIdentity energyNontrivial target e :=
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTiltSourceEnvelope_nonneg
      H β energyIdentity energyNontrivial hβ hEnergy target
  have hPartial :=
    finiteInfluenceKernelPartialSource_singleton_sum_source_le
      kernel hCard columnCoefficient hColumnNonneg hColumnSum
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTiltSourceEnvelope
        H β energyIdentity energyNontrivial target)
      hEnvelopeNonneg sourceMagnitude hMagnitude iterations
  rw [
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTiltSourceEnvelope_total
      H β energyIdentity energyNontrivial target] at hPartial
  have hTerminal :=
    finiteInfluenceKernelSingletonVariation_iterate_total_sum_source_le
      kernel hCard columnCoefficient hColumnNonneg hColumnSum
      sourceMagnitude hMagnitude iterations
  have hTerminalScaled :
      2 *
          (∑ source : FiniteEvenFourTorusSpatialLink H,
            finiteProductVariationTotal
              (finiteInfluenceKernelRandomScanVariationIterate
                kernel
                (finiteInfluenceKernelSingletonVariation
                  sourceMagnitude source)
                iterations)) ≤
        2 * (Fintype.card (FiniteEvenFourTorusSpatialLink H) : ℝ) *
          (finiteInfluenceKernelReciprocalRandomScanRate
              (FiniteEvenFourTorusSpatialLink H) columnCoefficient ^
            iterations * sourceMagnitude) := by
    calc
      2 *
          (∑ source : FiniteEvenFourTorusSpatialLink H,
            finiteProductVariationTotal
              (finiteInfluenceKernelRandomScanVariationIterate
                kernel
                (finiteInfluenceKernelSingletonVariation
                  sourceMagnitude source)
                iterations)) ≤
        2 *
          ((Fintype.card (FiniteEvenFourTorusSpatialLink H) : ℝ) *
            (finiteInfluenceKernelReciprocalRandomScanRate
                (FiniteEvenFourTorusSpatialLink H) columnCoefficient ^
              iterations * sourceMagnitude)) :=
        mul_le_mul_of_nonneg_left hTerminal (by norm_num)
      _ = 2 * (Fintype.card (FiniteEvenFourTorusSpatialLink H) : ℝ) *
          (finiteInfluenceKernelReciprocalRandomScanRate
              (FiniteEvenFourTorusSpatialLink H) columnCoefficient ^
            iterations * sourceMagnitude) := by ring
  unfold finiteEvenFourTorusZ2PerronPosteriorKernelResponseError
  simp_rw [
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedSourceTiltVariation_eq_singleton]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  apply (add_le_add hPartial hTerminalScaled).trans_eq
  unfold finiteEvenFourTorusZ2PerronPosteriorKernelFiniteResponseCoefficient
    finiteInfluenceKernelBidirectionalFiniteResponseCoefficient
  rfl

/-- Target-summed finite response controlled by a row coefficient, without
assuming that coefficient is strict. -/
theorem finiteEvenFourTorusZ2PerronPosteriorKernelResponseErrorColumnSum_le
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (kernel :
      FiniteNonnegativeInfluenceKernelData
        (FiniteEvenFourTorusSpatialLink H))
    (iterations : ℕ)
    (rowCoefficient : ℝ)
    (hRowNonneg : 0 ≤ rowCoefficient)
    (hRowSum :
      ∀ target : FiniteEvenFourTorusSpatialLink H,
        finiteInfluenceKernelRowSum kernel target ≤ rowCoefficient)
    (source : FiniteEvenFourTorusSpatialLink H) :
    (∑ target : FiniteEvenFourTorusSpatialLink H,
      finiteEvenFourTorusZ2PerronPosteriorKernelResponseError
        H β energyIdentity energyNontrivial
        kernel iterations target source) ≤
      finiteEvenFourTorusZ2PerronPosteriorKernelFiniteResponseCoefficient
        H β energyIdentity energyNontrivial iterations rowCoefficient := by
  let sourceMagnitude :=
    finiteZ2CrossingLikelihoodRatio
        (z2WilsonTemporalCrossingRate
          β energyIdentity energyNontrivial) -
      (finiteZ2CrossingLikelihoodRatio
        (z2WilsonTemporalCrossingRate
          β energyIdentity energyNontrivial))⁻¹
  let envelopeMagnitude :=
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTiltSourceAmplitude
      β energyIdentity energyNontrivial
  have hMagnitude : 0 ≤ sourceMagnitude :=
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedSourceTiltAmplitude_nonneg
      β energyIdentity energyNontrivial hβ hEnergy
  have hEnvelopeMagnitude : 0 ≤ envelopeMagnitude :=
    finiteEvenFourTorusZ2PerronPosteriorTargetTiltSourceAmplitude_nonneg
      β energyIdentity energyNontrivial hβ hEnergy
  have hCard :
      0 < Fintype.card (FiniteEvenFourTorusSpatialLink H) :=
    Fintype.card_pos_iff.mpr ⟨source⟩
  have hSingletonNonneg :
      ∀ e : FiniteEvenFourTorusSpatialLink H,
        0 ≤ finiteInfluenceKernelSingletonVariation sourceMagnitude source e := by
    intro e
    unfold finiteInfluenceKernelSingletonVariation
    split
    · exact hMagnitude
    · exact le_rfl
  have hPartial :=
    finiteInfluenceKernelPartialSource_singletonEnvelope_sum_target_le
      kernel hCard rowCoefficient hRowNonneg hRowSum
      envelopeMagnitude hEnvelopeMagnitude
      (finiteInfluenceKernelSingletonVariation sourceMagnitude source)
      hSingletonNonneg iterations
  rw [finiteInfluenceKernelSingletonVariation_total sourceMagnitude source] at hPartial
  have hTerminal :=
    finiteInfluenceKernelSingletonVariation_iterate_total_sum_target_le
      kernel hCard rowCoefficient hRowNonneg hRowSum
      sourceMagnitude hMagnitude source iterations
  have hTerminalScaled :
      2 *
          (∑ target : FiniteEvenFourTorusSpatialLink H,
            finiteProductVariationTotal
              (finiteInfluenceKernelRandomScanVariationIterate
                kernel
                (finiteInfluenceKernelSingletonVariation
                  sourceMagnitude source)
                iterations)) ≤
        2 * (Fintype.card (FiniteEvenFourTorusSpatialLink H) : ℝ) *
          (finiteInfluenceKernelReciprocalRandomScanRate
              (FiniteEvenFourTorusSpatialLink H) rowCoefficient ^
            iterations * sourceMagnitude) := by
    calc
      2 *
          (∑ target : FiniteEvenFourTorusSpatialLink H,
            finiteProductVariationTotal
              (finiteInfluenceKernelRandomScanVariationIterate
                kernel
                (finiteInfluenceKernelSingletonVariation
                  sourceMagnitude source)
                iterations)) ≤
        2 *
          ((Fintype.card (FiniteEvenFourTorusSpatialLink H) : ℝ) *
            (finiteInfluenceKernelReciprocalRandomScanRate
                (FiniteEvenFourTorusSpatialLink H) rowCoefficient ^
              iterations * sourceMagnitude)) :=
        mul_le_mul_of_nonneg_left hTerminal (by norm_num)
      _ = 2 * (Fintype.card (FiniteEvenFourTorusSpatialLink H) : ℝ) *
          (finiteInfluenceKernelReciprocalRandomScanRate
              (FiniteEvenFourTorusSpatialLink H) rowCoefficient ^
            iterations * sourceMagnitude) := by ring
  unfold finiteEvenFourTorusZ2PerronPosteriorKernelResponseError
  simp_rw [
    finiteEvenFourTorusZ2PerronPosteriorTargetTiltSourceEnvelope_eq_singleton,
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedSourceTiltVariation_eq_singleton]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  apply (add_le_add hPartial hTerminalScaled).trans_eq
  unfold finiteEvenFourTorusZ2PerronPosteriorKernelFiniteResponseCoefficient
    finiteInfluenceKernelBidirectionalFiniteResponseCoefficient
  rfl

end

end MathlibAnalytic
end MGAP4D
