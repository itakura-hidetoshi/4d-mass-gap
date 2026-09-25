import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkCanonicalFiberMeanKernelSectionIntegral
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferDiagonalProjectionKernelSectionIntegral
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkSplitDirectFiberBridge
import Mathlib.Tactic

/-!
# Canonical genuine fiber mean equals the diagonal remote projection

PR #4758 identifies the canonical genuine split-fiber mean, Haar-almost
everywhere in the retained outer context, with the literal fixed-right
kernel-section one-link expectation.

PR #4760 identifies the diagonal remote heat-bath projection pointwise with
the same kernel-section one-link expectation, expressed as a coordinate update.

The only remaining step is the pure coordinate identity saying that
reconstructing a right boundary from the retained off-target coordinates and a
target group value is the same as updating the canonical reconstructed
background at the target coordinate.

Thus the canonical genuine fiber mean agrees almost everywhere with the
diagonal remote projection.  No probability comparison, remote-separation
hypothesis, decay coefficient, or Poincare input is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory

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

/-- Haar-almost everywhere in the retained outer context, the canonical
one-link fiber mean is exactly the diagonal remote heat-bath projection
evaluated at the canonical right boundary reconstructed from the retained
coordinates. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean_ae_eq_diagonalRemoteProjection_rightFromOffTarget
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) :
    ∀ᵐ C ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
      ∀ᵐ retained ∂(Measure.pi
        (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
          normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))),
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean
            H N hN beta hbeta target F (C, retained) =
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
            H N hN beta hbeta C target source target
            (C source) (C target)
            (fun D => F (C, D))
            (periodicHypercubicEvenSpecialUnitarySpatialSliceRightFromOffTarget
              H N target retained) := by
  have hMean :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean_ae_eq_kernelSectionSpatialLinkIntegral
      H N hN beta hbeta target F hF
  filter_upwards [hMean] with C hC
  filter_upwards [hC] with retained hMeanRetained
  let A0 :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceRightFromOffTarget
      H N target retained
  let X :=
    fun D : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
      F (C, D)
  let eval :=
    periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target
  have hX : StronglyMeasurable X := by
    dsimp [X]
    exact hF.comp_measurable (measurable_const.prodMk measurable_id)
  have hOff :
      periodicHypercubicEvenSpatialSliceOffTargetRestriction target A0 =
        retained := by
    simpa [A0] using
      periodicHypercubicEvenSpecialUnitarySpatialSliceOffTargetRestriction_rightFromOffTarget
        H N target retained
  have hSection :
      ∀ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
        periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
            H N target F C retained g =
          X (Function.update A0 target g) := by
    intro g
    have hReconstruct :=
      periodicHypercubicEvenSpatialSliceTargetOffTarget_symm_offTargetRestriction_eq_update
        target A0 (eval.symm g)
    rw [hOff] at hReconstruct
    rw [eval.apply_symm_apply] at hReconstruct
    unfold periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
    exact congrArg (fun right => F (C, right)) hReconstruct
  have hIntegral :
      (∫ g,
        periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
          H N target F C retained g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
          H N hN beta hbeta C A0 target) =
      ∫ g,
        X (Function.update A0 target g)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
          H N hN beta hbeta C A0 target := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall hSection
  have hProjection :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_diagonal_eq_kernelSectionSpatialLinkIntegral
      H N hN beta hbeta C A0 target source X hX
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean
        H N hN beta hbeta target F (C, retained) =
      ∫ g,
        periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
          H N target F C retained g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
          H N hN beta hbeta C A0 target := by
      simpa [A0] using hMeanRetained
    _ =
      ∫ g,
        X (Function.update A0 target g)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
          H N hN beta hbeta C A0 target := hIntegral
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
        H N hN beta hbeta C target source target
        (C source) (C target) X A0 := hProjection.symm
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
        H N hN beta hbeta C target source target
        (C source) (C target)
        (fun D => F (C, D))
        (periodicHypercubicEvenSpecialUnitarySpatialSliceRightFromOffTarget
          H N target retained) := by
      rfl

end

end MathlibAnalytic
end MGAP4D
