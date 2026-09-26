import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferDiagonalReferenceFullKernelSectionLaw
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkCanonicalResidualVacuumKernelSectionAE
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkCanonicalFiberVarianceKernelSectionResidual
import Mathlib.Tactic

/-!
# Diagonal updated reference variance returns to the genuine target residual

PR #4796 identifies the stationarity-returned updated target variance with the
target heat-bath residual under the source reference law.

PR #4797 proves that at current-value parameters

  k  = C(distinguishedSource),
  g₂ = C(source),

that complete reference law and every one-link reference fiber are exactly the
fixed-right kernel-section laws, for an arbitrary resampled target.

This file integrates that diagonal identity over the physical vacuum and uses
the already-closed PR #4766 canonical-residual identity.  The result is exact:

  vacuum average of diagonal updated reference variance
    = canonical genuine target fiber variance.

It then reuses the existing coefficient-one canonical variance / genuine
CondExpL2 residual theorem.

No Harnack factor, factor two, response coefficient, remote-separation
hypothesis, or finite-cardinality loss is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance diagonalUpdatedVarianceGenuineResidualSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance diagonalUpdatedVarianceGenuineResidualSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance diagonalUpdatedVarianceGenuineResidualSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance diagonalUpdatedVarianceGenuineResidualSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance diagonalUpdatedVarianceGenuineResidualSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance diagonalUpdatedVarianceGenuineResidualSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- For one fixed physical-vacuum boundary C, the diagonal updated reference
variance is exactly the squared diagonal kernel-section target fluctuation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_referenceUpdatedBackgroundVarianceEnergy_diagonal_lintegral_eq_kernelSectionFluctuation_sq_lintegral
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (∫⁻ A,
      ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawUpdatedBackgroundVarianceEnergy
          H N hN beta hbeta C distinguishedSource source target
          (C distinguishedSource) (C source) F C A)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta C source distinguishedSource
        (C distinguishedSource) (C source)) =
      ∫⁻ A,
        ENNReal.ofReal
          ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
              H N hN beta hbeta C target source target
              (C source) (C target)
              (fun D => F (C, D)) A) ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta C := by
  let rightF :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    fun D => F (C, D)
  have hRightStrong : StronglyMeasurable rightF :=
    hF.comp_measurable (measurable_const.prodMk measurable_id)
  have hBase :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_reference_updatedBackgroundVarianceEnergy_lintegral_eq_referenceTargetResidual_sq_lintegral
      H N hN beta hbeta C distinguishedSource source target
      (C distinguishedSource) (C source) F hF bound hbound C
  calc
    (∫⁻ A,
      ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawUpdatedBackgroundVarianceEnergy
          H N hN beta hbeta C distinguishedSource source target
          (C distinguishedSource) (C source) F C A)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta C source distinguishedSource
        (C distinguishedSource) (C source)) =
      ∫⁻ A,
        ENNReal.ofReal
          ((F (C, A) -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection
                H N hN beta hbeta C source distinguishedSource target
                (C distinguishedSource) (C source) rightF A) ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta C source distinguishedSource
          (C distinguishedSource) (C source) := by
      simpa [rightF] using hBase
    _ =
      ∫⁻ A,
        ENNReal.ofReal
          ((F (C, A) -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection
                H N hN beta hbeta C source distinguishedSource target
                (C distinguishedSource) (C source) rightF A) ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta C := by
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_diagonalCurrentValues_eq_kernelSection
          H N hN beta hbeta C source distinguishedSource]
    _ =
      ∫⁻ A,
        ENNReal.ofReal
          ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
              H N hN beta hbeta C target source target
              (C source) (C target) rightF A) ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta C := by
      apply lintegral_congr
      intro A
      have hReferenceProjection :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection_diagonalCurrentValues_eq_kernelSectionSpatialLinkIntegral
          H N hN beta hbeta C A source distinguishedSource target
          rightF hRightStrong
      have hRemoteProjection :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_diagonal_eq_kernelSectionSpatialLinkIntegral
          H N hN beta hbeta C A target source rightF hRightStrong
      unfold
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
      rw [hReferenceProjection, hRemoteProjection]
    _ =
      ∫⁻ A,
        ENNReal.ofReal
          ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
              H N hN beta hbeta C target source target
              (C source) (C target)
              (fun D => F (C, D)) A) ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta C := by
      rfl

/-- Vacuum integration of the diagonal updated reference variance is exactly the
canonical genuine target fiber variance functional. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_vacuum_diagonal_referenceUpdatedBackgroundVarianceEnergy_lintegral_eq_canonicalFiberVarianceFunctional
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (∫⁻ C,
      (∫⁻ A,
        ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawUpdatedBackgroundVarianceEnergy
            H N hN beta hbeta C distinguishedSource source target
            (C distinguishedSource) (C source) F C A)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta C source distinguishedSource
          (C distinguishedSource) (C source))
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
        H N hN beta hbeta target F := by
  have hCanonical :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean_residual_ae_eq_diagonalRemoteKernelSectionFluctuation_vacuum_kernelSection
      H N hN beta hbeta target source F hF
  calc
    (∫⁻ C,
      (∫⁻ A,
        ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawUpdatedBackgroundVarianceEnergy
            H N hN beta hbeta C distinguishedSource source target
            (C distinguishedSource) (C source) F C A)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta C source distinguishedSource
          (C distinguishedSource) (C source))
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) =
      ∫⁻ C,
        (∫⁻ A,
          ENNReal.ofReal
            ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
                H N hN beta hbeta C target source target
                (C source) (C target)
                (fun D => F (C, D)) A) ^ 2)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta C)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta := by
      apply lintegral_congr
      intro C
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_referenceUpdatedBackgroundVarianceEnergy_diagonal_lintegral_eq_kernelSectionFluctuation_sq_lintegral
          H N hN beta hbeta C distinguishedSource source target
          F hF bound hbound
    _ =
      ∫⁻ C,
        (∫⁻ A,
          ENNReal.ofReal
            ((F (C, A) -
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean
                  H N hN beta hbeta target F
                  (C,
                    periodicHypercubicEvenSpatialSliceOffTargetRestriction
                      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
                      target A)) ^ 2)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta C)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta := by
      apply lintegral_congr_ae
      filter_upwards [hCanonical] with C hC
      apply lintegral_congr_ae
      filter_upwards [hC] with A hA
      rw [hA]
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
        H N hN beta hbeta target F := by
      symm
      simpa [
        periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional_eq_vacuum_kernelSection_canonicalFiberMean_residual_lintegral
          H N hN beta hbeta target F hF

/-- Coefficient-one genuine-residual bound for the diagonal updated reference
variance after vacuum integration. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_vacuum_diagonal_referenceUpdatedBackgroundVarianceEnergy_lintegral_le_condExpL2_residual_norm_sq
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (∫⁻ C,
      (∫⁻ A,
        ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawUpdatedBackgroundVarianceEnergy
            H N hN beta hbeta C distinguishedSource source target
            (C distinguishedSource) (C source) F C A)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta C source distinguishedSource
          (C distinguishedSource) (C source))
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) ≤
      ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
              H N hN beta hbeta F hF bound hbound -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
              H N hN beta hbeta target
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                H N hN beta hbeta F hF bound hbound)‖ ^ 2) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_vacuum_diagonal_referenceUpdatedBackgroundVarianceEnergy_lintegral_eq_canonicalFiberVarianceFunctional
      H N hN beta hbeta distinguishedSource source target F hF bound hbound]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional_le_condExpL2_residual_norm_sq
      H N hN beta hbeta target F hF bound hbound

end

end MGAP4D.MathlibAnalytic
