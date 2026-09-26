import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairSecondMeanRMSFeedbackAbsorption
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightHighTemperatureInfluence
import Mathlib.Tactic

/-!
# Canonical pin-free feedback coefficient is strict on the existing sweep interval

PR #4809 absorbs the second-mean RMS self-feedback under the explicit premise

  ofReal(K_pin(target,source)^2) < 1.

This file discharges that premise from the already-existing canonical
high-temperature weighted-column theorem.

Center the strict pin-free weighted column at the source.  The source weight
is exactly one, every target weight is at least one because s > 1, and every
kernel entry is nonnegative.  Hence each individual entry satisfies

  K_pin(target,source) < 1.

Squaring preserves strictness for the nonnegative entry and lifting through
ENNReal.ofReal gives the exact feedback premise required by PR #4809.

No new cutoff, response coefficient, Harnack factor, factor two, or
cardinality estimate is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance canonicalPinFreeFeedbackStrictSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance canonicalPinFreeFeedbackStrictSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance canonicalPinFreeFeedbackStrictSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance canonicalPinFreeFeedbackStrictSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance canonicalPinFreeFeedbackStrictSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance canonicalPinFreeFeedbackStrictSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Every entry of the canonical pin-free physical influence kernel is
strictly below one on the already-existing strict physical-sweep interval. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalPinFreePhysicalLeftKernel_influence_lt_one_of_strictPhysicalSweepCutoff
    (N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
        H beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
          H N hN beta hbeta)).influence target source < 1 := by
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
  have hHalfCut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s :=
    hcut.trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff_le_halfBarrierCutoff
        s)
  have hColumn :
      (∑ other : PeriodicHypercubicEvenSpatialSliceLink H,
        K.influence other source * W other) < 1 := by
    have h :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_exponentialWeightedColumn_lt_sourceWeight
        H N hN s (le_of_lt hs) beta hbeta hHalfCut source source
    have hSelf :
        W source = 1 := by
      simpa [W] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_self
          H s source
    simpa [K, W, hSelf] using h
  have hWeightNonneg :
      ∀ other : PeriodicHypercubicEvenSpatialSliceLink H, 0 ≤ W other := by
    intro other
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_nonneg
        H s (le_trans (by norm_num) (le_of_lt hs)) source other
  have hEntry :
      K.influence target source * W target ≤
        ∑ other : PeriodicHypercubicEvenSpatialSliceLink H,
          K.influence other source * W other := by
    exact
      Finset.single_le_sum
        (fun other _ =>
          mul_nonneg (K.influence_nonneg other source) (hWeightNonneg other))
        (Finset.mem_univ target)
  have hWeightOne : 1 ≤ W target := by
    dsimp [W,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight]
    exact one_le_pow₀ (le_of_lt hs)
  have hEntryLeWeighted :
      K.influence target source ≤ K.influence target source * W target := by
    calc
      K.influence target source =
          K.influence target source * 1 := by ring
      _ ≤ K.influence target source * W target :=
        mul_le_mul_of_nonneg_left hWeightOne
          (K.influence_nonneg target source)
  exact
    hEntryLeWeighted.trans_lt (hEntry.trans_lt hColumn)

/-- The squared canonical pin-free entry, lifted to ENNReal, is strictly below
one on the same existing strict physical-sweep interval. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalPinFreePhysicalLeftKernel_influence_sq_ofReal_lt_one_of_strictPhysicalSweepCutoff
    (N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    ENNReal.ofReal
        (((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
            H beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
              H N hN beta hbeta)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
              H N hN beta hbeta)).influence target source) ^ 2) < 1 := by
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
      H beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
        H N hN beta hbeta)
  have hK0 : 0 ≤ K.influence target source :=
    K.influence_nonneg target source
  have hK1 : K.influence target source < 1 := by
    simpa [K] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalPinFreePhysicalLeftKernel_influence_lt_one_of_strictPhysicalSweepCutoff
        N hN s hs beta hbeta hcut H target source
  have hSq : (K.influence target source) ^ 2 < (1 : ℝ) := by
    nlinarith [sq_nonneg (K.influence target source)]
  have hLift :
      ENNReal.ofReal ((K.influence target source) ^ 2) <
        ENNReal.ofReal (1 : ℝ) :=
    (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).2 hSq
  simpa [K] using hLift

/-- The PR #4809 absorbed RMS estimate with its strict feedback premise
discharged automatically by the existing strict physical-sweep cutoff. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_one_sub_canonicalPinFree_sq_ofReal_mul_secondMeanRMSAmplitudeL2_norm_sq_ofReal_le_harnackVariance_of_strictPhysicalSweepCutoff
    (N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 1 < s)
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
          (((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
              H beta hbeta
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
                H N hN beta hbeta)
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
                H N hN beta hbeta)).influence target source) ^ 2)) *
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
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_one_sub_canonicalPinFree_sq_ofReal_mul_secondMeanRMSAmplitudeL2_norm_sq_ofReal_le_harnackVariance
      N hN s hs beta hbeta hcut H B distinguishedSource source target hne
      k g₂ F hF bound hbound left
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalPinFreePhysicalLeftKernel_influence_sq_ofReal_lt_one_of_strictPhysicalSweepCutoff
        N hN s hs beta hbeta hcut H target source)

end

end MGAP4D.MathlibAnalytic
