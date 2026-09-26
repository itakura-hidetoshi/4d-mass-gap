import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairSecondMeanRMSFeedbackDischarge
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightHighTemperatureInfluence
import Mathlib.Tactic

/-!
# Uniformize the absorbed second-mean RMS feedback coefficient

PR #4810 discharges the pairwise strict feedback premise and proves

  (1 - ofReal(K_pin(target,source)^2)) * X <= A,

where X is the second-mean RMS L2 energy and A is the Harnack-weighted
stationarity-returned target variance.

For the target-indexed transpose recurrence, the left coefficient must no
longer depend on the ordered pair.  The existing canonical high-temperature
weighted-column theorem already supplies the common half-barrier scalar

  q_half(s,beta) < 1.

Centering that weighted column at its source and using W(source,source)=1 and
W(source,target)>=1 gives

  K_pin(target,source) < q_half(s,beta).

Hence

  ofReal(K_pin(target,source)^2) <= ofReal(q_half(s,beta)^2),

and therefore

  (1 - ofReal(q_half(s,beta)^2)) * X <= A.

No new cutoff, response coefficient, Harnack factor, factor two, or
cardinality factor is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance secondMeanRMSUniformFeedbackSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance secondMeanRMSUniformFeedbackSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance secondMeanRMSUniformFeedbackSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance secondMeanRMSUniformFeedbackSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance secondMeanRMSUniformFeedbackSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance secondMeanRMSUniformFeedbackSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Every canonical pin-free entry lies below the same half-barrier coefficient
on the existing strict physical-sweep interval. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_influence_lt_halfBarrierPinFreeCoefficient_of_strictPhysicalSweepCutoff
    (H N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
        H beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
          H N hN beta hbeta)).influence target source <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
        s beta := by
  classical
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
      H beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
        H N hN beta hbeta)
  let W :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
      H s source
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
      s beta
  have hHalfCut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s :=
    hcut.trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff_le_halfBarrierCutoff
        s)
  have hColumn :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_exponentialWeightedColumn_lt_halfBarrierCoefficient
      H N hN s hs.le beta hbeta hHalfCut source source
  have hSelf : W source = 1 := by
    simpa [W] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_self
        H s source
  have hColumnQ :
      (∑ x : PeriodicHypercubicEvenSpatialSliceLink H,
        K.influence x source * W x) < q := by
    simpa [K, W, q, hSelf] using hColumn
  have hWeightNonneg :
      ∀ x : PeriodicHypercubicEvenSpatialSliceLink H, 0 ≤ W x := by
    intro x
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_nonneg
        H s (le_trans (by norm_num) hs.le) source x
  have hEntry :
      K.influence target source * W target ≤
        ∑ x : PeriodicHypercubicEvenSpatialSliceLink H,
          K.influence x source * W x := by
    exact
      Finset.single_le_sum
        (fun x _ =>
          mul_nonneg (K.influence_nonneg x source) (hWeightNonneg x))
        (Finset.mem_univ target)
  have hWeightOne : 1 ≤ W target := by
    dsimp [W,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight]
    exact one_le_pow₀ hs.le
  have hEntryLeWeighted :
      K.influence target source ≤ K.influence target source * W target := by
    calc
      K.influence target source =
          K.influence target source * 1 := by simp
      _ ≤ K.influence target source * W target :=
        mul_le_mul_of_nonneg_left hWeightOne
          (K.influence_nonneg target source)
  have hEntryLt : K.influence target source < q :=
    hEntryLeWeighted.trans_lt (hEntry.trans_lt hColumnQ)
  simpa [K, q] using hEntryLt

/-- Uniform square comparison between an individual feedback coefficient and
the common half-barrier feedback coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_influence_sq_ofReal_le_halfBarrierPinFreeCoefficient_sq_ofReal_of_strictPhysicalSweepCutoff
    (H N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    ENNReal.ofReal
        (((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
            H beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
              H N hN beta hbeta)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
              H N hN beta hbeta)).influence target source) ^ 2) ≤
      ENNReal.ofReal
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
          s beta) ^ 2) := by
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
      H beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
        H N hN beta hbeta)
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
      s beta
  have hHalfCut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s :=
    hcut.trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff_le_halfBarrierCutoff
        s)
  have hK0 : 0 ≤ K.influence target source :=
    K.influence_nonneg target source
  have hq0 : 0 ≤ q :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient_nonneg_lt_one
      s beta hbeta hHalfCut).1
  have hKq : K.influence target source ≤ q := by
    exact le_of_lt
      (by
        simpa [K, q] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_influence_lt_halfBarrierPinFreeCoefficient_of_strictPhysicalSweepCutoff
            H N hN s hs beta hbeta hcut target source)
  have hSq :
      (K.influence target source) ^ 2 ≤ q ^ 2 :=
    (sq_le_sq₀ hK0 hq0).2 hKq
  simpa [K, q] using ENNReal.ofReal_le_ofReal hSq

/-- The common half-barrier feedback square remains strictly below one. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient_sq_ofReal_lt_one_of_strictPhysicalSweepCutoff
    (s : ℝ)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s) :
    ENNReal.ofReal
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
          s beta) ^ 2) < 1 := by
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
      s beta
  have hHalfCut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s :=
    hcut.trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff_le_halfBarrierCutoff
        s)
  have hq :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient_nonneg_lt_one
      s beta hbeta hHalfCut
  have hSq : q ^ 2 < (1 : ℝ) := by
    nlinarith [sq_nonneg q]
  have hLift :
      ENNReal.ofReal (q ^ 2) < ENNReal.ofReal (1 : ℝ) :=
    (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).2 hSq
  simpa [q] using hLift

/-- Uniformized absorbed RMS estimate: the pair-dependent feedback gap from
PR #4810 is weakened to the common half-barrier feedback gap. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_one_sub_halfBarrierPinFreeCoefficient_sq_ofReal_mul_secondMeanRMSAmplitudeL2_norm_sq_ofReal_le_harnackVariance
    (N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    (1 -
        ENNReal.ofReal
          ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
            s beta) ^ 2)) *
      ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2
            H N hN beta hbeta B distinguishedSource source target k g₂
            F hF bound hbound left‖ ^ 2) ≤
      (ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) + 1) *
        (∫⁻ A,
          ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawUpdatedBackgroundVarianceEnergy
              H N hN beta hbeta B distinguishedSource source target k g₂
              F left A)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
            H N hN beta hbeta B source distinguishedSource k g₂) := by
  let X : ℝ≥0∞ :=
    ENNReal.ofReal
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2
          H N hN beta hbeta B distinguishedSource source target k g₂
          F hF bound hbound left‖ ^ 2)
  let cPair : ℝ≥0∞ :=
    ENNReal.ofReal
      (((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
          H beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
            H N hN beta hbeta)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
            H N hN beta hbeta)).influence target source) ^ 2)
  let cUniform : ℝ≥0∞ :=
    ENNReal.ofReal
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
        s beta) ^ 2)
  have hPair :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_one_sub_canonicalPinFree_sq_ofReal_mul_secondMeanRMSAmplitudeL2_norm_sq_ofReal_le_harnackVariance_of_strictPhysicalSweepCutoff
      N hN s hs beta hbeta hcut H B distinguishedSource source target hne
      k g₂ F hF bound hbound left
  have hCoeff : cPair ≤ cUniform := by
    simpa [cPair, cUniform] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_influence_sq_ofReal_le_halfBarrierPinFreeCoefficient_sq_ofReal_of_strictPhysicalSweepCutoff
        H N hN s hs beta hbeta hcut target source
  have hGap :
      1 - cUniform ≤ 1 - cPair :=
    tsub_le_tsub_left hCoeff 1
  have hScaled :
      (1 - cUniform) * X ≤ (1 - cPair) * X := by
    simpa [mul_comm] using (mul_le_mul_right hGap X)
  exact hScaled.trans (by simpa [X, cPair, cUniform] using hPair)

end

end MGAP4D.MathlibAnalytic
