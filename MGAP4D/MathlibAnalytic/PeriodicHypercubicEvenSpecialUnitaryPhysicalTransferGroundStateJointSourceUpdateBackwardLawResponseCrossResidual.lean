import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceUpdateBackwardLawResponseL2Energy
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferVacuumResponseTargetMajorant
import Mathlib.Tactic

/-!
# Backward source-law response on the cross CondExp residual carrier

PR #4877 identifies, for every fixed current-value vacuum background `C`,
the backward source-law response energy on the actual target heat-bath
old/new joint carrier with the squared norm of the canonical target-law
response after transposing the geometric source/target indices.

This file integrates that exact identity over the physical vacuum law.  The
result is literally the already-existing vacuum response energy with

  response source = original target,
  response target = original source.

The existing target-majorant theorem can therefore be applied without any
response-symmetry assumption.  Its genuine conditional-expectation residual is

  ||F - Q_source F||^2,

so both branches of the backward direct fiber decomposition now land on the
same cross residual carrier:

* PR #4874: centered backward variance -> Harnack * ||F - Q_source F||^2;
* this file: backward law response -> K_pin(source,target)^2 * C_RMS
    * ||F - Q_source F||^2.

No finite-cardinality factor, arbitrary factor two, source/target exchange
assumption, or additional comparison coefficient is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance backwardLawResponseCrossResidualSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance backwardLawResponseCrossResidualSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance backwardLawResponseCrossResidualSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance backwardLawResponseCrossResidualSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance backwardLawResponseCrossResidualSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance backwardLawResponseCrossResidualSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Vacuum integration of PR #4877 is exactly the existing vacuum response
energy with geometric source/target indices transposed. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardLawResponse_currentValue_vacuum_lintegral_eq_transposedVacuumResponseL2Energy_of_bounded
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : source ≠ target)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (∫⁻ C,
      ∫⁻ CD,
        ENNReal.ofReal
          ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardLawResponse
            H N hN beta hbeta source F C C distinguishedSource
            (C distinguishedSource) (C source) CD) ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathJointMeasure
          H N hN beta hbeta C target distinguishedSource target
          (C distinguishedSource) (C target)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawVacuumResponseL2Energy
        H N hN beta hbeta distinguishedSource target source
        F hF bound hbound := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawVacuumResponseL2Energy
  apply lintegral_congr
  intro C
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardLawResponse_currentValue_heatBathJoint_lintegral_eq_transposedResponseL2_norm_sq_ofReal_of_bounded
      H N hN beta hbeta C distinguishedSource source target hne
      F hF bound hbound

/-- The vacuum backward law-response energy is controlled by the transposed
pin-free response coefficient and the genuine original-source CondExpL2
residual.  The coefficient orientation is `K_pin(source,target)`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardLawResponse_currentValue_vacuum_lintegral_le_transposedCanonicalPinFree_sq_mul_crossCondExpResidual
    (N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : source ≠ target)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (∫⁻ C,
      ∫⁻ CD,
        ENNReal.ofReal
          ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardLawResponse
            H N hN beta hbeta source F C C distinguishedSource
            (C distinguishedSource) (C source) CD) ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathJointMeasure
          H N hN beta hbeta C target distinguishedSource target
          (C distinguishedSource) (C target)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) ≤
      ENNReal.ofReal
          (((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
              H beta hbeta
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
                H N hN beta hbeta)
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
                H N hN beta hbeta)).influence source target) ^ 2) *
        ((1 -
            ENNReal.ofReal
              ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
                s beta) ^ 2))⁻¹ *
          ((ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) + 1) *
            ENNReal.ofReal
              (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                    H N hN beta hbeta F hF bound hbound -
                  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
                    H N hN beta hbeta source
                    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                      H N hN beta hbeta F hF bound hbound)‖ ^ 2))) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardLawResponse_currentValue_vacuum_lintegral_eq_transposedVacuumResponseL2Energy_of_bounded
      H N hN beta hbeta distinguishedSource source target hne
      F hF bound hbound]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_vacuumResponseL2Energy_le_canonicalPinFree_sq_ofReal_mul_feedbackGap_inv_mul_harnackFactor_add_one_mul_condExpL2_residual_norm_sq
      N hN s hs beta hbeta hcut H distinguishedSource target source hne
      F hF bound hbound

end

end MGAP4D.MathlibAnalytic
