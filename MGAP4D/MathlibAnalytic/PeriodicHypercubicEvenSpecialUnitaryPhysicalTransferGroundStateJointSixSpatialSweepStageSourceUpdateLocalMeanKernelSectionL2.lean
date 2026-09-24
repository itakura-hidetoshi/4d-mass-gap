import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageSourceUpdateLocalMeanKernelSectionCondExp
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumRemoteKernelSectionOneLinkProjectionL2
import MGAP4D.MathlibAnalytic.RealL2ExternalTensor
import Mathlib.Tactic

/-!
# Realize the physical diagonal local mean in the remote kernel-section L2 carrier

PR #4737 identifies the diagonal local source mean almost everywhere with the
source conditional-expectation defect under the actual fixed-right ground-state
kernel-section probability law.

The older remote kernel-section spine already provides the pointwise one-link
projection and fluctuation

  Q_source f = f - P_source f

together with its exact L2 preservation.

This file identifies the PR #4737 local mean with that existing fluctuation,
uses the canonical MemLp.toLp carrier, and records the exact squared-norm
integral identity.

No new conditional law, no ground-state joint disintegration, and no new
coefficient is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance localMeanKernelSectionL2SpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance localMeanKernelSectionL2SpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- A bounded concrete right section is L2 under the actual remote
kernel-section probability law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointKernelSectionRight_memLp_two_of_bounded
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (link distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    MemLp
      (fun C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        F (left, C))
      2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B distinguishedSource k) link g₂)) := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta
      (Function.update (Function.update B distinguishedSource k) link g₂)
  letI : IsProbabilityMeasure μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_isProbabilityMeasure
      H N hN beta hbeta
      (Function.update (Function.update B distinguishedSource k) link g₂)
  have hRight :
      StronglyMeasurable
        (fun C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          F (left, C)) :=
    hF.comp_measurable (measurable_const.prodMk measurable_id)
  apply MemLp.of_bound hRight.aestronglyMeasurable |bound|
  filter_upwards with C
  exact (hbound (left, C)).trans (le_abs_self bound)

/-- The diagonal local mean from PR #4737 is the same a.e. representative as
the canonical remote kernel-section one-link fluctuation from PR #4500. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalLocalMean_ae_eq_kernelSectionFluctuation_of_remote
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (link distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (hRefNe : link ≠ distinguishedSource)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette
        H link distinguishedSource)
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
        H N hN beta hbeta link F left B distinguishedSource k g₂ C) =ᵐ[
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B distinguishedSource k) link g₂)]
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
        H N hN beta hbeta B link distinguishedSource link k g₂
        (fun C => F (left, C)) := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta
      (Function.update (Function.update B distinguishedSource k) link g₂)
  let rightF :=
    fun C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
      F (left, C)
  have hRightLp : MemLp rightF 2 μ := by
    simpa [μ, rightF] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointKernelSectionRight_memLp_two_of_bounded
        H N hN beta hbeta B link distinguishedSource k g₂
        F hF bound hbound left
  have hRightInt : Integrable rightF μ :=
    memLp_one_iff_integrable.1 (hRightLp.mono_exponent one_le_two)
  have hLocal :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalLocalMean_ae_eq_kernelSection_condExp_defect_of_remote
      H N hN beta hbeta B link distinguishedSource
      hRefNe hNoShare k g₂ F hF bound hbound left
  have hProjection :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_ae_eq_condExp
      H N hN beta hbeta B
      (target := link) (source := distinguishedSource)
      hRefNe hNoShare link k g₂ rightF hRightInt
  filter_upwards [hLocal, hProjection] with C hLocalC hProjectionC
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
  rw [hLocalC, hProjectionC]
  rfl

/-- The existing remote kernel-section fluctuation is L2 for a bounded concrete
joint representative restricted to one fixed left configuration. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateKernelSectionFluctuation_memLp_two_of_remote
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (link distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (hRefNe : link ≠ distinguishedSource)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette
        H link distinguishedSource)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    MemLp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
        H N hN beta hbeta B link distinguishedSource link k g₂
        (fun C => F (left, C)))
      2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B distinguishedSource k) link g₂)) := by
  have hRight :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointKernelSectionRight_memLp_two_of_bounded
      H N hN beta hbeta B link distinguishedSource k g₂
      F hF bound hbound left
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation_memLp_two
      H N hN beta hbeta B
      (target := link) (source := distinguishedSource)
      hRefNe hNoShare link k g₂
      (fun C => F (left, C)) hRight

/-- Canonical L2 vector realizing the physical diagonal local mean on the
actual remote kernel-section probability carrier. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateLocalMeanKernelSectionL2
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (link distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (hRefNe : link ≠ distinguishedSource)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette
        H link distinguishedSource)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B distinguishedSource k) link g₂)) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateKernelSectionFluctuation_memLp_two_of_remote
    H N hN beta hbeta B link distinguishedSource hRefNe hNoShare
    k g₂ F hF bound hbound left).toLp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
        H N hN beta hbeta B link distinguishedSource link k g₂
        (fun C => F (left, C)))

/-- The canonical L2 vector has the physical diagonal local mean as an a.e.
representative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateLocalMeanKernelSectionL2_coeFn
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (link distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (hRefNe : link ≠ distinguishedSource)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette
        H link distinguishedSource)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateLocalMeanKernelSectionL2
        H N hN beta hbeta B link distinguishedSource hRefNe hNoShare
        k g₂ F hF bound hbound left =ᵐ[
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B distinguishedSource k) link g₂)]
      (fun C =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalLocalMean
          H N hN beta hbeta link F left B distinguishedSource k g₂ C) := by
  let hQ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateKernelSectionFluctuation_memLp_two_of_remote
      H N hN beta hbeta B link distinguishedSource hRefNe hNoShare
      k g₂ F hF bound hbound left
  have hQRep :=
    hQ.coeFn_toLp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
        H N hN beta hbeta B link distinguishedSource link k g₂
        (fun C => F (left, C)))
  have hLocal :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalLocalMean_ae_eq_kernelSectionFluctuation_of_remote
      H N hN beta hbeta B link distinguishedSource
      hRefNe hNoShare k g₂ F hF bound hbound left
  filter_upwards [hQRep, hLocal] with C hQC hLocalC
  rw [hQC, hLocalC]

/-- Exact squared-norm realization of the diagonal local mean on the remote
kernel-section probability carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateLocalMeanKernelSectionL2_norm_sq_eq_integral_sq
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (link distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (hRefNe : link ≠ distinguishedSource)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette
        H link distinguishedSource)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateLocalMeanKernelSectionL2
        H N hN beta hbeta B link distinguishedSource hRefNe hNoShare
        k g₂ F hF bound hbound left‖ ^ 2 =
      ∫ C,
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalLocalMean
          H N hN beta hbeta link F left B distinguishedSource k g₂ C) ^ 2
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta
          (Function.update (Function.update B distinguishedSource k) link g₂) := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta
      (Function.update (Function.update B distinguishedSource k) link g₂)
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateLocalMeanKernelSectionL2
      H N hN beta hbeta B link distinguishedSource hRefNe hNoShare
      k g₂ F hF bound hbound left
  letI : IsProbabilityMeasure μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_isProbabilityMeasure
      H N hN beta hbeta
      (Function.update (Function.update B distinguishedSource k) link g₂)
  have hRep :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateLocalMeanKernelSectionL2_coeFn
      H N hN beta hbeta B link distinguishedSource hRefNe hNoShare
      k g₂ F hF bound hbound left
  change ‖q‖ ^ 2 =
    ∫ C,
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalLocalMean
        H N hN beta hbeta link F left B distinguishedSource k g₂ C) ^ 2 ∂μ
  calc
    ‖q‖ ^ 2 = ∫ C, ‖q C‖ ^ 2 ∂μ :=
      realL2_norm_sq_eq_integral_norm_sq q
    _ = ∫ C,
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalLocalMean
          H N hN beta hbeta link F left B distinguishedSource k g₂ C) ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hRep] with C hC
      rw [hC]
      simp [Real.norm_eq_abs, sq_abs]

end

end MGAP4D.MathlibAnalytic
