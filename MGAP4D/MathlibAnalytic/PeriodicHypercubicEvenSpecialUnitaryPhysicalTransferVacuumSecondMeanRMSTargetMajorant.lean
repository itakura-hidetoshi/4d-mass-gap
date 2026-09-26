import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairSecondMeanRMSTargetResidualMajorant
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferDiagonalUpdatedVarianceGenuineResidual
import Mathlib.Tactic

/-!
# Vacuum-global target-indexed second-mean RMS majorant

PR #4813 removes the source index from the right-hand side of the fixed-boundary
absorbed RMS estimate by identifying every diagonal updated-reference variance
with one target-only kernel-section residual energy.

This file integrates that target-only quantity over the physical vacuum.

First we prove the exact identity

  ∫ TargetKernelSectionResidualEnergy(C,target,F) d nu_vac(C)
    =
  CanonicalFiberVarianceFunctional(target,F).

Then the PR #4813 pointwise estimate gives

  ∫ gap_fb * ofReal(||RMS2(C,source,target)||^2) d nu_vac(C)
    <=
  (K_H(beta)+1) * CanonicalFiberVarianceFunctional(target,F).

Finally the already-closed coefficient-one canonical variance / genuine
CondExpL2 residual comparison yields a source-independent target majorant in
the genuine joint carrier.

No new cutoff, response coefficient, Harnack factor, factor two, or
cardinality loss is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance vacuumSecondMeanRMSTargetMajorantSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance vacuumSecondMeanRMSTargetMajorantSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance vacuumSecondMeanRMSTargetMajorantSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance vacuumSecondMeanRMSTargetMajorantSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance vacuumSecondMeanRMSTargetMajorantSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance vacuumSecondMeanRMSTargetMajorantSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Vacuum integration of the source-independent fixed-boundary target residual
energy is exactly the canonical genuine target fiber variance functional. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy_vacuum_lintegral_eq_canonicalFiberVarianceFunctional
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (∫⁻ C,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy
        H N hN beta hbeta C target F
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
        H N hN beta hbeta target F := by
  have hBase :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_vacuum_diagonal_referenceUpdatedBackgroundVarianceEnergy_lintegral_eq_canonicalFiberVarianceFunctional
      H N hN beta hbeta target target target F hF bound hbound
  calc
    (∫⁻ C,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy
        H N hN beta hbeta C target F
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) =
      ∫⁻ C,
        (∫⁻ A,
          ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawUpdatedBackgroundVarianceEnergy
              H N hN beta hbeta C target target target
              (C target) (C target) F C A)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
            H N hN beta hbeta C target target
            (C target) (C target))
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta := by
      apply lintegral_congr
      intro C
      symm
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_referenceUpdatedBackgroundVarianceEnergy_diagonal_lintegral_eq_targetKernelSectionResidualEnergy
          H N hN beta hbeta C target target target
          F hF bound hbound
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
        H N hN beta hbeta target F :=
      hBase

/-- Vacuum-global target-indexed form of the PR #4813 absorbed RMS estimate.
The right-hand side is now the canonical genuine target fiber variance and is
independent of the source link. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_vacuum_diagonal_one_sub_halfBarrierPinFreeCoefficient_sq_ofReal_mul_secondMeanRMSAmplitudeL2_norm_sq_ofReal_lintegral_le_harnackFactor_add_one_mul_canonicalFiberVarianceFunctional
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
    (hne : target ≠ source)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (∫⁻ C,
      (1 -
          ENNReal.ofReal
            ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
              s beta) ^ 2)) *
        ENNReal.ofReal
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2
              H N hN beta hbeta C distinguishedSource source target
              (C distinguishedSource) (C source)
              F hF bound hbound C‖ ^ 2)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) ≤
      (ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) + 1) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
          H N hN beta hbeta target F := by
  let factor : ℝ≥0∞ :=
    ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) + 1
  let targetEnergy :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ≥0∞ :=
    fun C =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy
        H N hN beta hbeta C target F
  have hPoint :
      ∀ C,
        (1 -
            ENNReal.ofReal
              ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
                s beta) ^ 2)) *
          ENNReal.ofReal
            (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2
                H N hN beta hbeta C distinguishedSource source target
                (C distinguishedSource) (C source)
                F hF bound hbound C‖ ^ 2) ≤
          factor * targetEnergy C := by
    intro C
    simpa [factor, targetEnergy] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_diagonal_one_sub_halfBarrierPinFreeCoefficient_sq_ofReal_mul_secondMeanRMSAmplitudeL2_norm_sq_ofReal_le_harnackFactor_add_one_mul_targetKernelSectionResidualEnergy
        N hN s hs beta hbeta hcut H C distinguishedSource source target hne
        F hF bound hbound
  calc
    (∫⁻ C,
      (1 -
          ENNReal.ofReal
            ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
              s beta) ^ 2)) *
        ENNReal.ofReal
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2
              H N hN beta hbeta C distinguishedSource source target
              (C distinguishedSource) (C source)
              F hF bound hbound C‖ ^ 2)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) ≤
      ∫⁻ C, factor * targetEnergy C
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta :=
      lintegral_mono hPoint
    _ =
      factor *
        (∫⁻ C, targetEnergy C
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
            H N hN beta hbeta) := by
      rw [lintegral_const_mul']
      simp [factor]
    _ =
      (ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) + 1) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
          H N hN beta hbeta target F := by
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy_vacuum_lintegral_eq_canonicalFiberVarianceFunctional
          H N hN beta hbeta target F hF bound hbound]
      rfl

/-- Final global target-indexed RMS majorant in the genuine joint L2 carrier:
the only target quantity on the right is the genuine target conditional-
expectation residual norm-square. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_vacuum_diagonal_one_sub_halfBarrierPinFreeCoefficient_sq_ofReal_mul_secondMeanRMSAmplitudeL2_norm_sq_ofReal_lintegral_le_harnackFactor_add_one_mul_condExpL2_residual_norm_sq
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
    (hne : target ≠ source)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (∫⁻ C,
      (1 -
          ENNReal.ofReal
            ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
              s beta) ^ 2)) *
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
                  H N hN beta hbeta F hF bound hbound)‖ ^ 2) := by
  have hRMS :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_vacuum_diagonal_one_sub_halfBarrierPinFreeCoefficient_sq_ofReal_mul_secondMeanRMSAmplitudeL2_norm_sq_ofReal_lintegral_le_harnackFactor_add_one_mul_canonicalFiberVarianceFunctional
      N hN s hs beta hbeta hcut H distinguishedSource source target hne
      F hF bound hbound
  have hVariance :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional_le_condExpL2_residual_norm_sq
      H N hN beta hbeta target F hF bound hbound
  exact hRMS.trans
    (mul_le_mul_left'
      hVariance
      (ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) + 1))

end

end MGAP4D.MathlibAnalytic
