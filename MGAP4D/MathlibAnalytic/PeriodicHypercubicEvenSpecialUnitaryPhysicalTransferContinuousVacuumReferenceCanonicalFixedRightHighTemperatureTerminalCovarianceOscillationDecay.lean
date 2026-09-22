import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceDecay
import Mathlib.Tactic

/-!
# Canonical high-temperature terminal covariance decay with vanishing oscillations

This sharpens the already proved two-step terminal covariance decay without
changing the canonical high-temperature regime.

The two localized observables admit genuine oscillation bounds:

* the source Wilson crossing ratio lies in [exp(-2 beta), exp(2 beta)];
* the fixed-right target ratio lies in [exp(-16 beta), exp(16 beta)].

Therefore their singleton variation masses can be taken to be

  exp(2 beta) - exp(-2 beta)

and

  exp(16 beta) - exp(-16 beta),

respectively.  Both vanish at beta = 0.  Feeding these exact oscillations into
the existing canonical spatial covariance theorem gives a terminal covariance
prefactor which also vanishes at zero coupling.

No previously merged definition or theorem is modified.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

noncomputable section

local instance canonicalHighTemperatureTerminalCovarianceOscillationDecaySpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance canonicalHighTemperatureTerminalCovarianceOscillationDecaySpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance canonicalHighTemperatureTerminalCovarianceOscillationDecaySpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance canonicalHighTemperatureTerminalCovarianceOscillationDecaySpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance canonicalHighTemperatureTerminalCovarianceOscillationDecaySpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance canonicalHighTemperatureTerminalCovarianceOscillationDecaySpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Genuine singleton oscillation profile of the one-link Wilson crossing
ratio. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossingRatioOscillationVariation
    (H : ℕ)
    (beta : ℝ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    PeriodicHypercubicEvenSpatialSliceLink H → ℝ :=
  fun e =>
    if e = source then
      Real.exp (2 * beta) - Real.exp (-2 * beta)
    else 0

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossingRatioOscillationVariation_nonneg
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    ∀ e,
      0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossingRatioOscillationVariation
          H beta source e := by
  intro e
  by_cases he : e = source
  · subst e
    simp only [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossingRatioOscillationVariation,
      if_pos]
    exact
      sub_nonneg.mpr
        (Real.exp_le_exp.mpr (by linarith))
  · simp [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossingRatioOscillationVariation,
      he]

/-- The fixed-right target ratio also has the lower endpoint supplied by the
two pointwise exp(±8 beta) local-factor bounds. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_exp_neg_sixteen_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₁ g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Real.exp (-16 * beta) ≤
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta A B target g₁ /
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta A B target g₂ := by
  have hDenPos :
      0 <
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B target g₂ :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_pos
      H N beta A B target g₂
  apply (le_div_iff₀ hDenPos).2
  calc
    Real.exp (-16 * beta) *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B target g₂ ≤
      Real.exp (-16 * beta) * Real.exp (8 * beta) := by
        exact
          mul_le_mul_of_nonneg_left
            (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_le_exp_eight_mul
              H N hN beta hbeta A B target g₂)
            (Real.exp_nonneg _)
    _ = Real.exp (-8 * beta) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
        H N beta A B target g₁ :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_exp_neg_eight_mul_le
        H N hN beta hbeta A B target g₁

/-- Genuine singleton oscillation profile of the fixed-right target ratio. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioOscillationVariation
    (H : ℕ)
    (beta : ℝ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    PeriodicHypercubicEvenSpatialSliceLink H → ℝ :=
  fun e =>
    if e = target then
      Real.exp (16 * beta) - Real.exp (-16 * beta)
    else 0

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioOscillationVariation_nonneg
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    ∀ e,
      0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioOscillationVariation
          H beta target e := by
  intro e
  by_cases he : e = target
  · subst e
    simp only [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioOscillationVariation,
      if_pos]
    exact
      sub_nonneg.mpr
        (Real.exp_le_exp.mpr (by linarith))
  · simp [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioOscillationVariation,
      he]

/-- The fixed-right target-ratio coordinate variation is bounded by its actual
two-sided oscillation, not merely by its positive upper endpoint. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_oscillationVariation_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₁ g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    ∀ (e : PeriodicHypercubicEvenSpatialSliceLink H)
      (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
      |(periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta (Function.update C e u) B target g₁ /
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta (Function.update C e u) B target g₂) -
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta (Function.update C e v) B target g₁ /
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta (Function.update C e v) B target g₂)| ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioOscillationVariation
          H beta target e := by
  intro e C u v
  by_cases he : e = target
  · subst e
    have huLower :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_exp_neg_sixteen_le
        H N hN beta hbeta (Function.update C target u) B target g₁ g₂
    have hvLower :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_exp_neg_sixteen_le
        H N hN beta hbeta (Function.update C target v) B target g₁ g₂
    have huUpper :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_le_exp_sixteen
        H N hN beta hbeta (Function.update C target u) B target g₁ g₂
    have hvUpper :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_le_exp_sixteen
        H N hN beta hbeta (Function.update C target v) B target g₁ g₂
    simp only [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioOscillationVariation,
      if_pos]
    rw [abs_le]
    constructor <;> linarith
  · have hEq :
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                H N beta (Function.update C e u) B target g₁ /
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                H N beta (Function.update C e u) B target g₂ =
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                H N beta (Function.update C e v) B target g₁ /
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                H N beta (Function.update C e v) B target g₂ := by
        simp [
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor,
          Ne.symm he]
    rw [hEq, sub_self, abs_zero]
    simp [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioOscillationVariation,
      he]

/-- The sharpened terminal-covariance prefactor built from genuine localized
oscillations.  Unlike the coarse prefactor, it vanishes at beta = 0. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceOscillationPrefactor
    (s beta : ℝ) : ℝ :=
  2 *
    (1 -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
        s beta)⁻¹ *
    (Real.exp (2 * beta) - Real.exp (-2 * beta)) *
    (Real.exp (16 * beta) - Real.exp (-16 * beta))

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceOscillationPrefactor_zero
    (s : ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceOscillationPrefactor
      s 0 = 0 := by
  simp [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceOscillationPrefactor]

/-- The canonical two-step terminal covariance obeys the same spatial decay
ratio s⁻¹, now with a prefactor which vanishes at zero coupling. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTwoStepTerminalCovarianceSpatialBaseL1OscillationDecayBound
    (N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 1 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCovarianceSpatialBaseL1DecayBound
      N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceOscillationPrefactor
        s beta)
      s⁻¹ := by
  intro H B source target hTarget g₁ g₂ h k
  classical
  let mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta
      (Function.update (Function.update B source k) target g₂)
  let F :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    fun A =>
      specialUnitaryWilsonRelativeKernel N beta (A source) h /
        specialUnitaryWilsonRelativeKernel N beta (A source) k
  let G0 :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    fun A =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta A B target g₁ /
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta A B target g₂
  let G2 :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalObservable
      H N hN beta hbeta B target source g₁ g₂ k
  let variationF :
      PeriodicHypercubicEvenSpatialSliceLink H → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossingRatioOscillationVariation
      H beta source
  let variationG :
      PeriodicHypercubicEvenSpatialSliceLink H → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioOscillationVariation
      H beta target
  let D : ℕ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalSpatialBaseL1Distance
      H target source
  let Csp : ℝ :=
    (1 -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
        s beta)⁻¹ *
      (s ^ D)⁻¹ *
      (Real.exp (2 * beta) - Real.exp (-2 * beta)) *
      (Real.exp (16 * beta) - Real.exp (-16 * beta))
  have hRemote :
      target ∉ periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers
        H source source := by
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers] using
      hTarget
  rcases
    periodicHypercubicEvenSpatialSlice_not_mem_C5ExceptionalBackgroundFibers
      H source source target hRemote with
    ⟨hSourceTarget, _hTargetDistinguished, hNoShare⟩
  have hne : target ≠ source := Ne.symm hSourceTarget
  letI : IsProbabilityMeasure mu := by
    dsimp [mu]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source k) target g₂)
  have hFStrong : StronglyMeasurable F := by
    have hNum :
        Continuous
          (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
            specialUnitaryWilsonRelativeKernel N beta (A source) h) :=
      (continuous_specialUnitaryWilsonRelativeKernel N beta).comp₂
        (continuous_apply source) continuous_const
    have hDen :
        Continuous
          (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
            specialUnitaryWilsonRelativeKernel N beta (A source) k) :=
      (continuous_specialUnitaryWilsonRelativeKernel N beta).comp₂
        (continuous_apply source) continuous_const
    dsimp [F]
    exact
      (hNum.div hDen
        (fun A =>
          ne_of_gt
            (specialUnitaryWilsonRelativeKernel_pos hN hbeta (A source) k))).stronglyMeasurable
  have hGStrong : StronglyMeasurable G0 := by
    dsimp [G0]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_stronglyMeasurable
        H N beta B target g₁ g₂
  have hFMem : MemLp F 2 mu := by
    refine MemLp.of_bound hFStrong.aestronglyMeasurable
      (Real.exp (2 * beta)) ?_
    filter_upwards [] with A
    have hBounds :=
      specialUnitaryWilsonRelativeKernel_ratio_mem_Icc_exp_neg_two_exp_two
        N hN beta hbeta (A source) h k
    have hPos :
        0 <
          specialUnitaryWilsonRelativeKernel N beta (A source) h /
            specialUnitaryWilsonRelativeKernel N beta (A source) k :=
      div_pos
        (specialUnitaryWilsonRelativeKernel_pos hN hbeta (A source) h)
        (specialUnitaryWilsonRelativeKernel_pos hN hbeta (A source) k)
    dsimp [F]
    rw [abs_of_pos hPos]
    exact hBounds.2
  have hGMem : MemLp G0 2 mu := by
    refine MemLp.of_bound hGStrong.aestronglyMeasurable
      (Real.exp (16 * beta)) ?_
    filter_upwards [] with A
    have hPos :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_pos
        H N beta A B target g₁ g₂
    have hBound :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_le_exp_sixteen
        H N hN beta hbeta A B target g₁ g₂
    dsimp [G0]
    rw [abs_of_pos hPos]
    exact hBound
  have hVariationFNonneg : ∀ e, 0 ≤ variationF e := by
    simpa [variationF] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossingRatioOscillationVariation_nonneg
        H beta hbeta source
  have hVariationGNonneg : ∀ e, 0 ≤ variationG e := by
    simpa [variationG] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioOscillationVariation_nonneg
        H beta hbeta target
  have hVariationF :
      ∀ (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
        |F (Function.update C e u) - F (Function.update C e v)| ≤
          variationF e := by
    intro e C u v
    by_cases he : e = source
    · subst e
      have hu :=
        specialUnitaryWilsonRelativeKernel_ratio_mem_Icc_exp_neg_two_exp_two
          N hN beta hbeta u h k
      have hv :=
        specialUnitaryWilsonRelativeKernel_ratio_mem_Icc_exp_neg_two_exp_two
          N hN beta hbeta v h k
      have hOsc :
          |(specialUnitaryWilsonRelativeKernel N beta u h /
                specialUnitaryWilsonRelativeKernel N beta u k) -
            (specialUnitaryWilsonRelativeKernel N beta v h /
                specialUnitaryWilsonRelativeKernel N beta v k)| ≤
            Real.exp (2 * beta) - Real.exp (-2 * beta) := by
        rw [abs_le]
        constructor <;> linarith
      simpa [
        F,
        variationF,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossingRatioOscillationVariation] using
        hOsc
    · have hse : source ≠ e := Ne.symm he
      simp [
        F,
        variationF,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossingRatioOscillationVariation,
        he,
        hse]
  have hVariationG :
      ∀ (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
        |G0 (Function.update C e u) - G0 (Function.update C e v)| ≤
          variationG e := by
    simpa [G0, variationG] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_oscillationVariation_le
        H N hN beta hbeta B target g₁ g₂
  have hSeparated :
      ∀ left right : PeriodicHypercubicEvenSpatialSliceLink H,
        variationF left ≠ 0 →
        variationG right ≠ 0 →
          D ≤
            periodicHypercubicEdgeBaseL1Distance
              (PeriodicHypercubicEvenSideLength H)
              (periodicHypercubicEvenSpatialSliceLinkEmbedding H left)
              (periodicHypercubicEvenSpatialSliceLinkEmbedding H right) := by
    intro left right hLeft hRight
    have hLeftEq : left = source := by
      by_contra hls
      apply hLeft
      simp [
        variationF,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossingRatioOscillationVariation,
        hls]
    have hRightEq : right = target := by
      by_contra hrt
      apply hRight
      simp [
        variationG,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioOscillationVariation,
        hrt]
    subst left
    subst right
    dsimp [D,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalSpatialBaseL1Distance]
    exact
      (periodicHypercubicEdgeBaseL1Distance_comm
        (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H source)).le
  have hGOsc :
      ∀ X Y : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        |G0 X - G0 Y| ≤
          Real.exp (16 * beta) - Real.exp (-16 * beta) := by
    intro X Y
    have hXLower :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_exp_neg_sixteen_le
        H N hN beta hbeta X B target g₁ g₂
    have hYLower :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_exp_neg_sixteen_le
        H N hN beta hbeta Y B target g₁ g₂
    have hXUpper :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_le_exp_sixteen
        H N hN beta hbeta X B target g₁ g₂
    have hYUpper :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_le_exp_sixteen
        H N hN beta hbeta Y B target g₁ g₂
    dsimp [G0]
    rw [abs_le]
    constructor <;> linarith
  have hGOscNonneg :
      0 ≤ Real.exp (16 * beta) - Real.exp (-16 * beta) := by
    exact
      sub_nonneg.mpr
        (Real.exp_le_exp.mpr (by linarith))
  have hFullRaw :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSection_realIntegralCovariance_abs_le_canonicalHighTemperatureSpatial
      H N hN s hs.le beta hbeta hcut B hne hNoShare g₂ k F G0
      hFStrong hGStrong hFMem hGMem variationF variationG
      hVariationFNonneg hVariationGNonneg hVariationF hVariationG
      D hSeparated
      (Real.exp (16 * beta) - Real.exp (-16 * beta)) hGOscNonneg hGOsc
  have hPartialRaw :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionRestrictedRandomScan_realIntegralCovariance_partial_telescope_abs_le_canonicalHighTemperatureSpatial
      H N hN s hs.le beta hbeta hcut B hne hNoShare g₂ k F G0
      hFStrong hGStrong hFMem hGMem variationF variationG
      hVariationFNonneg hVariationGNonneg hVariationF hVariationG
      D hSeparated 2
  have hSumF :
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, variationF e) =
        Real.exp (2 * beta) - Real.exp (-2 * beta) := by
    simp [
      variationF,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossingRatioOscillationVariation]
  have hSumG :
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, variationG e) =
        Real.exp (16 * beta) - Real.exp (-16 * beta) := by
    simp [
      variationG,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioOscillationVariation]
  have hFull :
      |realIntegralCovariance mu F G0| ≤ Csp := by
    simpa [mu, Csp, hSumF, hSumG] using hFullRaw
  have hPartial :
      |realIntegralCovariance mu F G0 -
        realIntegralCovariance mu F G2| ≤ Csp := by
    simpa [
      mu,
      G0,
      G2,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalObservable,
      Csp,
      hSumF,
      hSumG] using hPartialRaw
  have hTerminal :
      |realIntegralCovariance mu F G2| ≤ 2 * Csp := by
    have hEq :
        realIntegralCovariance mu F G2 =
          realIntegralCovariance mu F G0 -
            (realIntegralCovariance mu F G0 -
              realIntegralCovariance mu F G2) := by
      ring
    rw [hEq]
    calc
      |realIntegralCovariance mu F G0 -
          (realIntegralCovariance mu F G0 -
            realIntegralCovariance mu F G2)| ≤
        |realIntegralCovariance mu F G0| +
          |realIntegralCovariance mu F G0 -
            realIntegralCovariance mu F G2| :=
        abs_sub _ _
      _ ≤ Csp + Csp :=
        add_le_add hFull hPartial
      _ = 2 * Csp := by ring
  calc
    |realIntegralCovariance
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta
          (Function.update (Function.update B source k) target g₂))
        (fun A =>
          specialUnitaryWilsonRelativeKernel N beta (A source) h /
            specialUnitaryWilsonRelativeKernel N beta (A source) k)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalObservable
          H N hN beta hbeta B target source g₁ g₂ k)| ≤
      2 * Csp := by
        simpa [mu, F, G2] using hTerminal
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceOscillationPrefactor
          s beta *
        (s⁻¹) ^
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalSpatialBaseL1Distance
            H target source := by
      dsimp [
        Csp,
        D,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceOscillationPrefactor]
      rw [inv_pow]
      ring

/-- The sharpened terminal covariance prefactor is nonnegative throughout the
same canonical high-temperature interval. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceOscillationPrefactor_nonneg
    (s beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceOscillationPrefactor
        s beta := by
  have hq :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient_nonneg_lt_one
      s beta hbeta hcut
  have hGapNonneg :
      0 ≤
        1 -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
            s beta :=
    sub_nonneg.mpr hq.2.le
  have hCross :
      0 ≤ Real.exp (2 * beta) - Real.exp (-2 * beta) :=
    sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))
  have hTarget :
      0 ≤ Real.exp (16 * beta) - Real.exp (-16 * beta) :=
    sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceOscillationPrefactor
  exact
    mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (by norm_num)
          (inv_nonneg.mpr hGapNonneg))
        hCross)
      hTarget

end

end MGAP4D.MathlibAnalytic
