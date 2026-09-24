import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageSourceUpdateBackwardDirectMeanSplit
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumRemoteKernelSectionOneLinkRCD
import Mathlib.Tactic

/-!
# Identify the diagonal local mean with a genuine conditional-expectation defect

PR #4736 splits the backward direct mean into a diagonal local term and a pure
conditional-law response. This file identifies the diagonal term exactly.

Pointwise, the diagonal local mean is

  F(left,C) - integral F(left,D) K_source(C,dD),

where K_source is the full continuous-vacuum reference source heat-bath kernel.

Under the existing remote reference/kernel-section identification, the same
heat-bath integral is an actual conditional-expectation representative for the
fixed-right ground-state kernel-section law. Thus the local term becomes a
literal source one-link conditional-expectation defect on that genuine
kernel-section probability carrier.

The remote hypothesis here concerns the reference-law parameters source and
distinguishedSource; it is not silently identified with any other target/source
pair from the outer sweep geometry.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance localMeanKernelSectionSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance localMeanKernelSectionSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance localMeanKernelSectionSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance localMeanKernelSectionSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance localMeanKernelSectionSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance localMeanKernelSectionSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The diagonal local mean from PR #4736 is exactly the source heat-bath
conditional-expectation defect at the same background. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalLocalMean_eq_value_sub_heatBathIntegral
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left B C :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalLocalMean
        H N hN beta hbeta source F left B distinguishedSource k g₂ C =
      F (left, C) -
        ∫ D, F (left, D)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
            H N hN beta hbeta B source distinguishedSource source k g₂ C := by
  let ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta B source distinguishedSource source k g₂ C
  letI : IsProbabilityMeasure ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
      H N hN beta hbeta B source distinguishedSource source k g₂ C
  have hUpdate :
      Measurable
        (fun v : Matrix.specialUnitaryGroup (Fin N) ℂ =>
          Function.update C source v) :=
    measurable_update C
  have hRight :
      StronglyMeasurable
        (fun D : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          F (left, D)) :=
    hF.comp_measurable (measurable_const.prodMk measurable_id)
  have hUpdated :
      StronglyMeasurable
        (fun v : Matrix.specialUnitaryGroup (Fin N) ℂ =>
          F (left, Function.update C source v)) :=
    hRight.comp_measurable hUpdate
  have hUpdatedInt :
      Integrable
        (fun v : Matrix.specialUnitaryGroup (Fin N) ℂ =>
          F (left, Function.update C source v)) ν := by
    refine Integrable.mono'
      (integrable_const (μ := ν) |bound|)
      hUpdated.aestronglyMeasurable ?_
    filter_upwards [] with v
    exact
      (hbound (left, Function.update C source v)).trans
        (le_abs_self bound)
  have hConstInt :
      Integrable
        (fun _v : Matrix.specialUnitaryGroup (Fin N) ℂ => F (left, C)) ν :=
    integrable_const _
  have hHeat :
      (∫ D, F (left, D)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
          H N hN beta hbeta B source distinguishedSource source k g₂ C) =
        ∫ v, F (left, Function.update C source v) ∂ν := by
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_apply_eq_map
        H N hN beta hbeta B source distinguishedSource source k g₂ C]
    exact
      MeasureTheory.integral_map
        hUpdate.aemeasurable hRight.aestronglyMeasurable
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalLocalMean
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateFullConfigurationDifference
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel_apply]
  change
    (∫ v, (F (left, C) - F (left, Function.update C source v)) ∂ν) =
      F (left, C) -
        ∫ D, F (left, D)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
            H N hN beta hbeta B source distinguishedSource source k g₂ C
  rw [integral_sub hConstInt hUpdatedInt]
  rw [integral_const, probReal_univ, one_smul]
  rw [hHeat]

/-- Under the existing remote full-law identification, the diagonal local mean
is almost everywhere the genuine source conditional-expectation defect on the
fixed-right ground-state kernel-section probability law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalLocalMean_ae_eq_kernelSection_condExp_defect_of_remote
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source distinguishedSource :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hRefNe : source ≠ distinguishedSource)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette
        H source distinguishedSource)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    (fun C =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalLocalMean
        H N hN beta hbeta source F left B distinguishedSource k g₂ C) =ᵐ[
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update
          (Function.update B distinguishedSource k) source g₂)]
      (fun C =>
        F (left, C) -
          MeasureTheory.condExp
            (periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace
              H N source)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
              H N hN beta hbeta
              (Function.update
                (Function.update B distinguishedSource k) source g₂))
            (fun D => F (left, D)) C) := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta
      (Function.update (Function.update B distinguishedSource k) source g₂)
  let rightF :=
    fun D : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
      F (left, D)
  letI : IsProbabilityMeasure μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_isProbabilityMeasure
      H N hN beta hbeta
      (Function.update (Function.update B distinguishedSource k) source g₂)
  have hRight : StronglyMeasurable rightF := by
    dsimp [rightF]
    exact hF.comp_measurable (measurable_const.prodMk measurable_id)
  have hRightInt : Integrable rightF μ := by
    refine Integrable.mono'
      (integrable_const (μ := μ) |bound|)
      hRight.aestronglyMeasurable ?_
    filter_upwards [] with D
    exact (hbound (left, D)).trans (le_abs_self bound)
  have hCond :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel_ae_eq_kernelSection_condExp_of_remote
      H N hN beta hbeta B
      (target := source) (source := distinguishedSource)
      hRefNe hNoShare source k g₂ rightF hRightInt
  filter_upwards [hCond] with C hC
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalLocalMean_eq_value_sub_heatBathIntegral
      H N hN beta hbeta source F hF bound hbound
      left B C distinguishedSource k g₂]
  rw [
    ← periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel_apply
      H N hN beta hbeta B source distinguishedSource source k g₂ C]
  simpa [μ, rightF] using congrArg (fun x : ℝ => F (left, C) - x) hC

end

end MGAP4D.MathlibAnalytic
