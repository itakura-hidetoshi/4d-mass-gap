import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairSecondMeanRMSHarnackResponseBound
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferVacuumFirstCrossGenuineResidual
import Mathlib.Tactic

/-!
# Vacuum-integrated second-mean RMS energy controlled by the genuine target residual

PR #4805 gives, for each fixed outer background C,

  ofReal(||RMS2(C)||^2)
    <= (K_H(beta)+1) * updatedReferenceVariance(C)
       + ofReal(||ResponseL2(C)||^2).

PR #4798 identifies the vacuum average of the diagonal updated-reference
variance with the canonical genuine target variance and bounds it by the
genuine target CondExpL2 residual norm-square. PR #4799 supplies exactly the
outer a.e.-measurability needed to split the lower integral.

This file therefore proves

  integral_vac ofReal(||RMS2(C)||^2)
    <= (K_H(beta)+1) * ofReal(||F-CondExp_target F||^2)
       + integral_vac ofReal(||ResponseL2(C)||^2).

The response term is deliberately left untouched. No new Harnack factor,
factor two, response coefficient, remote-separation hypothesis, or cardinality
loss is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance vacuumSecondMeanRMSGenuineResidualSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance vacuumSecondMeanRMSGenuineResidualSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance vacuumSecondMeanRMSGenuineResidualSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance vacuumSecondMeanRMSGenuineResidualSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance vacuumSecondMeanRMSGenuineResidualSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance vacuumSecondMeanRMSGenuineResidualSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Vacuum-integrated second-mean RMS energy bound with the updated-variance
term returned to the genuine target CondExpL2 residual. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_vacuum_diagonal_secondMeanRMSAmplitudeL2_norm_sq_lintegral_le_harnackLawFactor_add_one_mul_condExpL2_residual_norm_sq_add_responseL2_norm_sq_lintegral
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (∫⁻ C,
      ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2
            H N hN beta hbeta C distinguishedSource source target
            (C distinguishedSource) (C source)
            F hF bound hbound C‖ ^ 2)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) ≤
      (ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) + 1) *
        ENNReal.ofReal
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                H N hN beta hbeta F hF bound hbound -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
                H N hN beta hbeta target
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                  H N hN beta hbeta F hF bound hbound)‖ ^ 2) +
      (∫⁻ C,
        ENNReal.ofReal
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
              H N hN beta hbeta C distinguishedSource source target
              (C distinguishedSource) (C source)
              F hF bound hbound C 0‖ ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta) := by
  let ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
      H N hN beta hbeta
  let K : ℝ≥0∞ :=
    ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2)
  let rmsSq :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ≥0∞ :=
    fun C =>
      ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2
            H N hN beta hbeta C distinguishedSource source target
            (C distinguishedSource) (C source)
            F hF bound hbound C‖ ^ 2)
  let variance :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ≥0∞ :=
    fun C =>
      ∫⁻ A,
        ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawUpdatedBackgroundVarianceEnergy
            H N hN beta hbeta C distinguishedSource source target
            (C distinguishedSource) (C source) F C A)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta C source distinguishedSource
          (C distinguishedSource) (C source)
  let responseSq :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ≥0∞ :=
    fun C =>
      ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
            H N hN beta hbeta C distinguishedSource source target
            (C distinguishedSource) (C source)
            F hF bound hbound C 0‖ ^ 2)
  let targetResidualSq : ℝ≥0∞ :=
    ENNReal.ofReal
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
            H N hN beta hbeta F hF bound hbound -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN beta hbeta target
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
              H N hN beta hbeta F hF bound hbound)‖ ^ 2)
  have hPoint : ∀ C, rmsSq C ≤ (K + 1) * variance C + responseSq C := by
    intro C
    simpa [rmsSq, K, variance, responseSq] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2_norm_sq_ofReal_le_harnackLawFactor_add_one_mul_referenceUpdatedVariance_add_responseL2_norm_sq
        H N hN beta hbeta C distinguishedSource source target hne
        (C distinguishedSource) (C source)
        F hF bound hbound C
  have hVarianceAE : AEMeasurable variance ν := by
    simpa [variance, ν] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_diagonal_referenceUpdatedBackgroundVariance_outer_aemeasurable
        H N hN beta hbeta distinguishedSource source target
        F hF bound hbound
  have hScaledVarianceAE :
      AEMeasurable (fun C => (K + 1) * variance C) ν :=
    hVarianceAE.const_mul (K + 1)
  have hVarianceBound :
      (∫⁻ C, variance C ∂ν) ≤ targetResidualSq := by
    simpa [variance, ν, targetResidualSq] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_vacuum_diagonal_referenceUpdatedBackgroundVarianceEnergy_lintegral_le_condExpL2_residual_norm_sq
        H N hN beta hbeta distinguishedSource source target
        F hF bound hbound
  have hIntegrated :
      (∫⁻ C, rmsSq C ∂ν) ≤
        ∫⁻ C, (K + 1) * variance C + responseSq C ∂ν :=
    lintegral_mono hPoint
  have hSplit :
      (∫⁻ C, (K + 1) * variance C + responseSq C ∂ν) =
        (K + 1) * (∫⁻ C, variance C ∂ν) +
          ∫⁻ C, responseSq C ∂ν := by
    rw [lintegral_add_left' hScaledVarianceAE]
    rw [lintegral_const_mul'' (K + 1) hVarianceAE]
  have hScaledVarianceBound :
      (K + 1) * (∫⁻ C, variance C ∂ν) ≤
        (K + 1) * targetResidualSq :=
    mul_le_mul_right hVarianceBound (K + 1)
  calc
    (∫⁻ C,
      ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2
            H N hN beta hbeta C distinguishedSource source target
            (C distinguishedSource) (C source)
            F hF bound hbound C‖ ^ 2)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) =
      ∫⁻ C, rmsSq C ∂ν := by
        rfl
    _ ≤ ∫⁻ C, (K + 1) * variance C + responseSq C ∂ν :=
      hIntegrated
    _ = (K + 1) * (∫⁻ C, variance C ∂ν) +
          ∫⁻ C, responseSq C ∂ν :=
      hSplit
    _ ≤ (K + 1) * targetResidualSq +
          ∫⁻ C, responseSq C ∂ν :=
      add_le_add hScaledVarianceBound (le_refl _)
    _ =
      (ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) + 1) *
        ENNReal.ofReal
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                H N hN beta hbeta F hF bound hbound -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
                H N hN beta hbeta target
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                  H N hN beta hbeta F hF bound hbound)‖ ^ 2) +
        (∫⁻ C,
          ENNReal.ofReal
            (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
                H N hN beta hbeta C distinguishedSource source target
                (C distinguishedSource) (C source)
                F hF bound hbound C 0‖ ^ 2)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
            H N hN beta hbeta) := by
      rfl

end

end MGAP4D.MathlibAnalytic
