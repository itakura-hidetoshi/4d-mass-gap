import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairSecondMeanRMSSelfFeedback
import Mathlib.Tactic

/-!
# Absorb strict second-mean RMS self-feedback

PR #4808 proves the fixed-background self-feedback inequality

  X <= A + c * X,

where

  X = ofReal(||RMS2L2||^2),
  A = (K_H(beta)+1) * updatedReferenceVariance,
  c = ofReal(K_pin(target,source)^2).

This file performs only the ENNReal algebra needed to absorb that feedback
under the explicit strict hypothesis c < 1.

Because X is an ofReal value, it is finite. Hence c * X is finite as well,
and the common right summand may be cancelled safely after rewriting

  X = (1-c) * X + c * X.

The result is

  (1-c) * X <= A.

No new analytic estimate, cutoff, Harnack factor, factor two, response
coefficient, or cardinality factor is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance secondMeanRMSFeedbackAbsorptionSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance secondMeanRMSFeedbackAbsorptionSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance secondMeanRMSFeedbackAbsorptionSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance secondMeanRMSFeedbackAbsorptionSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance secondMeanRMSFeedbackAbsorptionSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance secondMeanRMSFeedbackAbsorptionSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Generic finite-ENNReal absorption lemma used by the concrete RMS theorem
below. -/
theorem ennreal_one_sub_mul_le_of_le_add_mul_self
    (X A c : ℝ≥0∞)
    (hXTop : X ≠ ⊤)
    (hc : c < 1)
    (hSelf : X ≤ A + c * X) :
    (1 - c) * X ≤ A := by
  have hcTop : c ≠ ⊤ :=
    ne_of_lt (hc.trans ENNReal.one_lt_top)
  have hcXTop : c * X ≠ ⊤ :=
    ENNReal.mul_ne_top hcTop hXTop
  have hDecomp :
      (1 - c) * X + c * X = X := by
    rw [← add_mul]
    rw [tsub_add_cancel_of_le (le_of_lt hc)]
    simp
  have hAdd :
      (1 - c) * X + c * X ≤ A + c * X := by
    rw [hDecomp]
    exact hSelf
  exact ENNReal.le_of_add_le_add_right hcXTop hAdd

/-- Concrete absorption of the PR #4808 second-mean RMS self-feedback term. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_one_sub_canonicalPinFree_sq_ofReal_mul_secondMeanRMSAmplitudeL2_norm_sq_ofReal_le_harnackVariance
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
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (hFeedback :
      ENNReal.ofReal
          (((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
              H beta hbeta
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
                H N hN beta hbeta)
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
                H N hN beta hbeta)).influence target source) ^ 2) < 1) :
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
  let X : ℝ≥0∞ :=
    ENNReal.ofReal
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2
          H N hN beta hbeta B distinguishedSource source target k g₂
          F hF bound hbound left‖ ^ 2)
  let c : ℝ≥0∞ :=
    ENNReal.ofReal
      (((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
          H beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
            H N hN beta hbeta)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
            H N hN beta hbeta)).influence target source) ^ 2)
  let A : ℝ≥0∞ :=
    (ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) + 1) *
      (∫⁻ A,
        ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawUpdatedBackgroundVarianceEnergy
            H N hN beta hbeta B distinguishedSource source target k g₂
            F left A)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta B source distinguishedSource k g₂)
  have hSelf : X ≤ A + c * X := by
    simpa [X, A, c] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2_norm_sq_ofReal_le_harnackVariance_add_canonicalPinFree_sq_mul_self
        N hN s hs beta hbeta hcut H B distinguishedSource source target hne
        k g₂ F hF bound hbound left
  have hXTop : X ≠ ⊤ := by
    dsimp [X]
    exact ENNReal.ofReal_ne_top
  have hAbsorb :=
    ennreal_one_sub_mul_le_of_le_add_mul_self X A c hXTop
      (by simpa [c] using hFeedback) hSelf
  simpa [X, A, c] using hAbsorb

end

end MGAP4D.MathlibAnalytic
