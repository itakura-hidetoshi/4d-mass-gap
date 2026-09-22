import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightHighTemperatureSpatialCovarianceClustering
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceTwoStepTerminalCovarianceSpatialBaseL1DecayBridge
import Mathlib.Tactic

/-!
# Canonical high-temperature two-step terminal covariance decay

The canonical spatial covariance theorem applies directly to the two localized
observables before the terminal smoothing step:

* the source Wilson crossing ratio, supported on the source coordinate;
* the fixed-right target-ratio observable, supported on the target coordinate.

The exact terminal observable is the two-step restricted-random-scan smoothing
of the second observable.  Therefore its covariance with the source crossing
ratio is bounded by the sum of

* the full unsmoothed covariance; and
* the M = 2 covariance-telescope difference.

Both terms obey the same canonical spatial clustering estimate.  This yields
an explicit two-step terminal covariance decay certificate with ratio s^{-1}
at every fixed scale s > 1, using only the original cutoff at that same scale.

No shell summation, remote residual estimate, Poincare/coercivity statement,
Hamiltonian gap, or continuum construction is asserted in this file.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

noncomputable section

local instance canonicalHighTemperatureTerminalCovarianceDecaySpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance canonicalHighTemperatureTerminalCovarianceDecaySpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance canonicalHighTemperatureTerminalCovarianceDecaySpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance canonicalHighTemperatureTerminalCovarianceDecaySpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance canonicalHighTemperatureTerminalCovarianceDecaySpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance canonicalHighTemperatureTerminalCovarianceDecaySpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Periodic base-L1 distance is symmetric. -/
theorem periodicHypercubicEdgeBaseL1Distance_comm
    (n : ℕ)
    (a b : PeriodicHypercubicEdge n) :
    periodicHypercubicEdgeBaseL1Distance n a b =
      periodicHypercubicEdgeBaseL1Distance n b a := by
  unfold periodicHypercubicEdgeBaseL1Distance
  unfold periodicHypercubicVertexL1Distance
  apply Finset.sum_congr rfl
  intro i _hi
  have hsub :
      a.1 i - b.1 i = -(b.1 i - a.1 i) := by
    abel
  rw [hsub]
  exact
    (ZMod.natAbs_valMinAbs_neg (b.1 i - a.1 i)).symm

/-- Singleton source variation profile for the one-link Wilson crossing ratio. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossingRatioVariation
    (H : ℕ)
    (beta : ℝ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    PeriodicHypercubicEvenSpatialSliceLink H → ℝ :=
  fun e => if e = source then Real.exp (2 * beta) else 0

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossingRatioVariation_nonneg
    (H : ℕ)
    (beta : ℝ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    ∀ e,
      0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossingRatioVariation
          H beta source e := by
  intro e
  by_cases he : e = source
  · subst e
    simp [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossingRatioVariation,
      Real.exp_nonneg]
  · simp [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossingRatioVariation,
      he]

/-- The canonical terminal-covariance prefactor.  The leading factor two comes
from combining the full unsmoothed covariance with its two-step telescope
difference. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovariancePrefactor
    (s beta : ℝ) : ℝ :=
  2 *
    (1 -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
        s beta)⁻¹ *
    Real.exp (2 * beta) *
    Real.exp (16 * beta)

/-- The concrete canonical high-temperature covariance theorem discharges the
abstract two-step terminal covariance spatial-decay obligation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTwoStepTerminalCovarianceSpatialBaseL1DecayBound
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
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovariancePrefactor
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
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossingRatioVariation
      H beta source
  let variationG :
      PeriodicHypercubicEvenSpatialSliceLink H → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
      H beta target
  let D : ℕ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalSpatialBaseL1Distance
      H target source
  let Csp : ℝ :=
    (1 -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
        s beta)⁻¹ *
      (s ^ D)⁻¹ *
      Real.exp (2 * beta) *
      Real.exp (16 * beta)
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
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossingRatioVariation_nonneg
        H beta source
  have hVariationGNonneg : ∀ e, 0 ≤ variationG e := by
    simpa [variationG] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_nonneg
        H beta target
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
      have hu0 :
          0 ≤
            specialUnitaryWilsonRelativeKernel N beta u h /
              specialUnitaryWilsonRelativeKernel N beta u k :=
        (Real.exp_pos (-2 * beta)).le.trans hu.1
      have hv0 :
          0 ≤
            specialUnitaryWilsonRelativeKernel N beta v h /
              specialUnitaryWilsonRelativeKernel N beta v k :=
        (Real.exp_pos (-2 * beta)).le.trans hv.1
      simpa [
        F,
        variationF,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossingRatioVariation] using
        (abs_sub_le_of_nonneg_of_le hu0 hu.2 hv0 hv.2)
    · have hse : source ≠ e := Ne.symm he
      simp [
        F,
        variationF,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossingRatioVariation,
        he,
        hse]
  have hVariationG :
      ∀ (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
        |G0 (Function.update C e u) - G0 (Function.update C e v)| ≤
          variationG e := by
    simpa [G0, variationG] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_variation_le
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
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossingRatioVariation,
        hls]
    have hRightEq : right = target := by
      by_contra hrt
      apply hRight
      simp [
        variationG,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation,
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
        |G0 X - G0 Y| ≤ Real.exp (16 * beta) := by
    intro X Y
    have hXPos :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_pos
        H N beta X B target g₁ g₂
    have hYPos :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_pos
        H N beta Y B target g₁ g₂
    have hXLe :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_le_exp_sixteen
        H N hN beta hbeta X B target g₁ g₂
    have hYLe :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_le_exp_sixteen
        H N hN beta hbeta Y B target g₁ g₂
    dsimp [G0]
    exact
      abs_sub_le_of_nonneg_of_le hXPos.le hXLe hYPos.le hYLe
  have hFullRaw :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSection_realIntegralCovariance_abs_le_canonicalHighTemperatureSpatial
      H N hN s hs.le beta hbeta hcut B hne hNoShare g₂ k F G0
      hFStrong hGStrong hFMem hGMem variationF variationG
      hVariationFNonneg hVariationGNonneg hVariationF hVariationG
      D hSeparated
      (Real.exp (16 * beta)) (Real.exp_nonneg _) hGOsc
  have hPartialRaw :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionRestrictedRandomScan_realIntegralCovariance_partial_telescope_abs_le_canonicalHighTemperatureSpatial
      H N hN s hs.le beta hbeta hcut B hne hNoShare g₂ k F G0
      hFStrong hGStrong hFMem hGMem variationF variationG
      hVariationFNonneg hVariationGNonneg hVariationF hVariationG
      D hSeparated 2
  have hSumF :
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, variationF e) =
        Real.exp (2 * beta) := by
    simp [
      variationF,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossingRatioVariation]
  have hSumG :
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, variationG e) =
        Real.exp (16 * beta) := by
    simp [
      variationG,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation]
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
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovariancePrefactor
          s beta *
        (s⁻¹) ^
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalSpatialBaseL1Distance
            H target source := by
      dsimp [
        Csp,
        D,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovariancePrefactor]
      rw [inv_pow]
      ring


/-- The explicit canonical terminal-covariance prefactor is nonnegative on the
same high-temperature interval. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovariancePrefactor_nonneg
    (s beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovariancePrefactor
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
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovariancePrefactor
  exact
    mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (by norm_num)
          (inv_nonneg.mpr hGapNonneg))
        (Real.exp_nonneg _))
      (Real.exp_nonneg _)


end

end MGAP4D.MathlibAnalytic
