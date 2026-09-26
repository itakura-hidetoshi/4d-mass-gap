import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairCurrentValueOffDiagonalOuterSchurInterface
import Mathlib.Tactic

/-!
# Canonical assembled current-value source state

PR #4827 reduces the concrete current-value outer-Schur interface to two
observable-specific inputs: an exact finite decomposition and an off-diagonal
second-mean RMS majorant by the target state norm.

The decomposition carries no independent analytic content once the localPart
and target-law response vectors are fixed.  This file therefore defines the
canonical source state to be exactly

  assembledState(C,A,source)
    = localPart(C,A,source)
      + sum_target response(C,A,source,target).

The decomposition required by PR #4827 is then definitional.  Consequently the
only remaining nontrivial interface for the outer transpose Schur route is

  ||RMS2(C,A,source,target)||
    <= ||assembledState(C,A,target)||

for off-diagonal target/source pairs, almost everywhere in the outer
kernel-section background.

No new estimate, response coefficient, factor two, pin-free replacement, or
finite-cardinality factor is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

local instance canonicalAssembledCurrentValueStateSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance canonicalAssembledCurrentValueStateSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Canonical current-value state in the source-dependent fixed-background L2
carrier: the diagonal localPart plus the complete finite target-law response
sum. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalAssembledCurrentValueFixedBackgroundL2
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointCurrentValueFixedBackgroundSourcePairL2
      H N hN beta hbeta C A distinguishedSource source :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalPartFixedBackgroundL2
      H N hN beta hbeta C A distinguishedSource source F +
    ∑ target,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseCurrentValueFixedBackgroundL2
        H N hN beta hbeta C A distinguishedSource source target
        F hF bound hbound C

/-- The canonical assembled state has the exact decomposition required by the
dependent normed-response assembler. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalAssembledCurrentValueFixedBackgroundL2_eq_localPart_add_sum_response
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalAssembledCurrentValueFixedBackgroundL2
        H N hN beta hbeta C A distinguishedSource source
        F hF bound hbound =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalPartFixedBackgroundL2
          H N hN beta hbeta C A distinguishedSource source F +
        ∑ target,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseCurrentValueFixedBackgroundL2
            H N hN beta hbeta C A distinguishedSource source target
            F hF bound hbound C := by
  rfl

/-- With the canonical assembled state, the exact decomposition premise
disappears completely.  Only the off-diagonal RMS-to-target-state majorant
remains before the outer transpose Schur receiver closes. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalAssembledCurrentValue_aeOuterLIntegralTransposeSchurReceiver_of_offDiagonalSecondMeanRMSMajorant
    (N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (hRMSMajorant :
      ∀ᵐ A
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta C,
        ∀ source target,
          target ≠ source →
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeCurrentValueFixedBackgroundL2
              H N hN beta hbeta C A distinguishedSource source target
              F hF bound hbound C‖ ≤
            ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalAssembledCurrentValueFixedBackgroundL2
              H N hN beta hbeta C A distinguishedSource target
              F hF bound hbound‖) :
    (∫⁻ A, ENNReal.ofReal
      ((1 -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient
          s beta) ^ 2 *
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalAssembledCurrentValueFixedBackgroundL2
            H N hN beta hbeta C A distinguishedSource e
            F hF bound hbound‖ ^ 2)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta C) ≤
      ∫⁻ A, ENNReal.ofReal
        (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalMean
            H N hN beta hbeta C A distinguishedSource e F| ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta C := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCurrentValue_aeOuterLIntegralTransposeSchurReceiver_of_decomposition_and_offDiagonalSecondMeanRMSMajorant
      N hN s hs beta hbeta hcut H C distinguishedSource
      F hF bound hbound
      (fun A source =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalAssembledCurrentValueFixedBackgroundL2
          H N hN beta hbeta C A distinguishedSource source
          F hF bound hbound)
      (by
        filter_upwards with A
        intro source
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalAssembledCurrentValueFixedBackgroundL2_eq_localPart_add_sum_response
            H N hN beta hbeta C A distinguishedSource source
            F hF bound hbound)
      hRMSMajorant

end

end MGAP4D.MathlibAnalytic
