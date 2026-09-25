import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkCanonicalResidualVacuumKernelSectionAE
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkCanonicalFiberVarianceKernelSectionResidual
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSourceUpdateDiagonalKernelSectionL2
import Mathlib.Tactic

/-!
# Canonical variance as vacuum-averaged diagonal section L2 energy

PR #4766 descends the canonical residual / diagonal remote fluctuation identity
to the actual physical vacuum and literal fixed-right kernel-section laws.

The diagonal section carrier from PR #4748 is definitionally the L2 class of
that same remote fluctuation.  Therefore the canonical genuine one-link fiber
variance is exactly the physical-vacuum average of the squared norms of the
canonical diagonal section vectors.

Combining this exact identity with the already-established coefficient-one
canonical variance / genuine CondExpL2 residual inequality yields the integrated
localPart energy bound required before packaging the source-specific assembler
carrier.

No comparison coefficient, response estimate, or Poincare input is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

attribute [local instance]
  groundStateJointOneLinkBoundedCoreSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkBoundedCoreSpecialUnitaryCompactSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkBoundedCoreSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitaryBorelSpace
  groundStateJointOneLinkBoundedCoreSpatialLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkUnique

/-- The canonical genuine target-fiber variance is exactly the physical-vacuum
average of the squared norms of the canonical diagonal section L2 carriers. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional_eq_vacuum_diagonalLocalMeanKernelSectionL2_norm_sq_lintegral
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hRefNe : target ≠ source)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
        H N hN beta hbeta target F =
      ∫⁻ C,
        ENNReal.ofReal
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalOuterLocalMeanKernelSectionL2
              H N hN beta hbeta C target source hRefNe hNoShare
              F hF bound hbound‖ ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta := by
  have hBase :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional_eq_vacuum_kernelSection_canonicalFiberMean_residual_lintegral
      H N hN beta hbeta target F hF
  have hAE :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean_residual_ae_eq_diagonalRemoteKernelSectionFluctuation_vacuum_kernelSection
      H N hN beta hbeta target source F hF
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
        H N hN beta hbeta target F =
      ∫⁻ C,
        (∫⁻ A,
          ENNReal.ofReal
            ((F (C, A) -
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean
                  H N hN beta hbeta target F
                  (C,
                    periodicHypercubicEvenSpatialSliceOffTargetRestriction
                      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target A)) ^ 2)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta C)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta := by
      simpa [
        periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap]
        using hBase
    _ =
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
      apply lintegral_congr_ae
      filter_upwards [hAE] with C hC
      apply lintegral_congr_ae
      filter_upwards [hC] with A hA
      rw [hA]
    _ =
      ∫⁻ C,
        ENNReal.ofReal
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalOuterLocalMeanKernelSectionL2
              H N hN beta hbeta C target source hRefNe hNoShare
              F hF bound hbound‖ ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta := by
      apply lintegral_congr_ae
      filter_upwards with C
      let μ :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta C
      let q :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
          H N hN beta hbeta C target source target
          (C source) (C target)
          (fun D => F (C, D))
      let r :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalOuterLocalMeanKernelSectionL2
          H N hN beta hbeta C target source hRefNe hNoShare
          F hF bound hbound
      have hq :
          MemLp q 2 μ := by
        simpa [q, μ] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalOuterKernelSectionFluctuation_memLp_two
            H N hN beta hbeta C target source hRefNe hNoShare
            F hF bound hbound
      have hqSq :
          Integrable (fun A => q A ^ 2) μ := by
        simpa only [Pi.pow_apply] using hq.integrable_sq
      have hRep :
          (fun A => r A) =ᵐ[μ] q := by
        simpa [r, q, μ,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalOuterLocalMeanKernelSectionL2] using
          hq.coeFn_toLp
      have hReal :
          (∫ A, q A ^ 2 ∂μ) = ‖r‖ ^ 2 := by
        calc
          (∫ A, q A ^ 2 ∂μ) =
              ∫ A, ‖r A‖ ^ 2 ∂μ := by
            apply integral_congr_ae
            filter_upwards [hRep] with A hA
            rw [hA]
            simp [Real.norm_eq_abs, sq_abs]
          _ = ‖r‖ ^ 2 :=
            (realL2_norm_sq_eq_integral_norm_sq r).symm
      calc
        (∫⁻ A, ENNReal.ofReal (q A ^ 2) ∂μ) =
            ENNReal.ofReal (∫ A, q A ^ 2 ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal
            hqSq (ae_of_all μ fun A => sq_nonneg (q A))).symm
        _ = ENNReal.ofReal (‖r‖ ^ 2) := by
          rw [hReal]
        _ =
          ENNReal.ofReal
            (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalOuterLocalMeanKernelSectionL2
                H N hN beta hbeta C target source hRefNe hNoShare
                F hF bound hbound‖ ^ 2) := by
          rfl

/-- Coefficient-one integrated localPart energy bound: the vacuum-averaged
diagonal section L2 energy is bounded by the genuine one-link CondExpL2
residual norm squared. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLink_vacuum_diagonalLocalMeanKernelSectionL2_norm_sq_lintegral_le_condExpL2_residual_norm_sq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hRefNe : target ≠ source)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (∫⁻ C,
      ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalOuterLocalMeanKernelSectionL2
            H N hN beta hbeta C target source hRefNe hNoShare
            F hF bound hbound‖ ^ 2)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) ≤
      ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
              H N hN beta hbeta F hF bound hbound -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
              H N hN beta hbeta target
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                H N hN beta hbeta F hF bound hbound)‖ ^ 2) := by
  calc
    (∫⁻ C,
      ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalOuterLocalMeanKernelSectionL2
            H N hN beta hbeta C target source hRefNe hNoShare
            F hF bound hbound‖ ^ 2)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
        H N hN beta hbeta target F := by
      symm
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional_eq_vacuum_diagonalLocalMeanKernelSectionL2_norm_sq_lintegral
          H N hN beta hbeta target source hRefNe hNoShare
          F hF bound hbound
    _ ≤
      ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
              H N hN beta hbeta F hF bound hbound -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
              H N hN beta hbeta target
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                H N hN beta hbeta F hF bound hbound)‖ ^ 2) :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional_le_condExpL2_residual_norm_sq
        H N hN beta hbeta target F hF bound hbound

end

end MathlibAnalytic
end MGAP4D
