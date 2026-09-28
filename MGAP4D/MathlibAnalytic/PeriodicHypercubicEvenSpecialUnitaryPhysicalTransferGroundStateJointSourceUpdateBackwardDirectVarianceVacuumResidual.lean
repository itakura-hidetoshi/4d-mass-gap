import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceUpdateBackwardDirectVarianceJointResidual
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairTargetResidualVacuumSum
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferDiagonalReferenceFullKernelSectionLaw
import Mathlib.Tactic

/-!
# Vacuum closure of the backward direct variance

PR #4873 controls the backward centered direct variance, averaged over the
actual target heat-bath old/new joint law, by the normalized Harnack factor
times the source one-link residual under the source reference law.

At current-value parameters the complete source reference law is exactly the
fixed-right kernel-section law, and its source heat-bath projection is exactly
the genuine kernel-section source conditional expectation.  Therefore the
remaining source residual is the already-existing target-kernel-section
residual energy with target = source.

After physical-vacuum integration this is exactly the canonical genuine source
fiber variance, and hence is bounded with coefficient one by the genuine
source CondExpL2 residual norm square.

No target summation, source summation, finite-cardinality factor, response
symmetry, factor two, or additional comparison coefficient is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance backwardDirectVarianceVacuumResidualSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance backwardDirectVarianceVacuumResidualSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance backwardDirectVarianceVacuumResidualSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance backwardDirectVarianceVacuumResidualSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance backwardDirectVarianceVacuumResidualSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance backwardDirectVarianceVacuumResidualSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- At current-value parameters, the source-reference residual from PR #4873
is exactly the genuine fixed-right kernel-section source residual energy. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdate_referenceSourceResidual_currentValue_eq_targetKernelSectionResidualEnergy
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) :
    (∫⁻ A,
      ENNReal.ofReal
        ((F (C, A) -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection
              H N hN beta hbeta C source distinguishedSource source
              (C distinguishedSource) (C source)
              (fun D => F (C, D)) A) ^ 2)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta C source distinguishedSource
        (C distinguishedSource) (C source)) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy
        H N hN beta hbeta C source F := by
  let rightF :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    fun D => F (C, D)
  have hRightStrong : StronglyMeasurable rightF :=
    hF.comp_measurable (measurable_const.prodMk measurable_id)
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_diagonalCurrentValues_eq_kernelSection
      H N hN beta hbeta C source distinguishedSource]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy
  apply lintegral_congr
  intro A
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection_diagonalCurrentValues_eq_kernelSectionSpatialLinkIntegral
      H N hN beta hbeta C A source distinguishedSource source
      rightF hRightStrong]

/-- Vacuum integration of the backward direct variance, after averaging over
one off-source target heat-bath transition, is bounded by the normalized
Harnack factor times the exact canonical genuine source fiber variance. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy_currentValue_vacuum_lintegral_le_harnackLawFactor_mul_canonicalSourceFiberVariance
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
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
            H N hN beta hbeta source F C C distinguishedSource
            (C distinguishedSource) (C source) CD)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathJointMeasure
          H N hN beta hbeta C source distinguishedSource target
          (C distinguishedSource) (C source)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) ≤
      ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
          H N hN beta hbeta source F := by
  let ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
      H N hN beta hbeta
  let K : ℝ≥0∞ := ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2)
  let varianceEnergy :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ≥0∞ :=
    fun C =>
      ∫⁻ CD,
        ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
            H N hN beta hbeta source F C C distinguishedSource
            (C distinguishedSource) (C source) CD)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathJointMeasure
          H N hN beta hbeta C source distinguishedSource target
          (C distinguishedSource) (C source)
  let sourceResidual :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ≥0∞ :=
    fun C =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy
        H N hN beta hbeta C source F
  have hPoint : ∀ C, varianceEnergy C ≤ K * sourceResidual C := by
    intro C
    have hBase :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy_heatBathJoint_lintegral_le_harnackLawFactor_mul_referenceSourceResidual_of_bounded
        H N hN beta hbeta C distinguishedSource source target hne
        (C distinguishedSource) (C source)
        F hF bound hbound C
    have hResidual :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdate_referenceSourceResidual_currentValue_eq_targetKernelSectionResidualEnergy
        H N hN beta hbeta C distinguishedSource source F hF
    simpa [varianceEnergy, sourceResidual, K] using
      hBase.trans_eq (congrArg (fun x : ℝ≥0∞ => K * x) hResidual)
  have hResidualAE : AEMeasurable sourceResidual ν := by
    simpa [sourceResidual, ν] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy_aemeasurable_vacuum
        H N hN beta hbeta source F hF
  have hResidualIntegral :
      (∫⁻ C, sourceResidual C ∂ν) =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
          H N hN beta hbeta source F := by
    simpa [sourceResidual, ν] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy_vacuum_lintegral_eq_canonicalFiberVarianceFunctional
        H N hN beta hbeta source F hF bound hbound
  calc
    (∫⁻ C, varianceEnergy C ∂ν) ≤
        ∫⁻ C, K * sourceResidual C ∂ν :=
      lintegral_mono hPoint
    _ = K * ∫⁻ C, sourceResidual C ∂ν := by
      rw [lintegral_const_mul'' K hResidualAE]
    _ = K *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
          H N hN beta hbeta source F := by
      rw [hResidualIntegral]
    _ =
      ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
          H N hN beta hbeta source F := by
      rfl

/-- Coefficient-one genuine CondExpL2 closure of the same backward-variance
term.  The only coefficient is the already-existing normalized Harnack factor. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy_currentValue_vacuum_lintegral_le_harnackLawFactor_mul_condExpL2_sourceResidual
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
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
            H N hN beta hbeta source F C C distinguishedSource
            (C distinguishedSource) (C source) CD)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathJointMeasure
          H N hN beta hbeta C source distinguishedSource target
          (C distinguishedSource) (C source)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) ≤
      ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) *
        ENNReal.ofReal
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                H N hN beta hbeta F hF bound hbound -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
                H N hN beta hbeta source
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                  H N hN beta hbeta F hF bound hbound)‖ ^ 2) := by
  have hVariance :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy_currentValue_vacuum_lintegral_le_harnackLawFactor_mul_canonicalSourceFiberVariance
      H N hN beta hbeta distinguishedSource source target hne
      F hF bound hbound
  have hResidual :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional_le_condExpL2_residual_norm_sq
      H N hN beta hbeta source F hF bound hbound
  exact
    hVariance.trans
      (mul_le_mul_right
        hResidual
        (ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2)))

end

end MGAP4D.MathlibAnalytic
