import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkCanonicalFiberMeanKernelSectionIntegral
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferDiagonalReferenceFiberKernelSectionLaw
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumRemoteKernelSectionOneLinkProjection
import Mathlib.Tactic

/-!
# Canonical genuine fiber mean equals the diagonal remote kernel-section projection

PR #4758 identifies the canonical genuine target-fiber mean with the literal
fixed-right kernel-section one-link integral.  PR #4759 identifies the
diagonal continuous-vacuum reference target-fiber law with that same literal
kernel-section one-link law.

This file closes the remaining coordinate step:

* the diagonal remote heat-bath projection is pointwise the kernel-section
  one-link integral;
* Haar-almost-everywhere in the genuine outer split coordinates, the canonical
  fiber mean equals that diagonal remote projection;
* consequently the canonical centered residual is exactly the already-defined
  remote kernel-section fluctuation.

No remote-separation estimate, comparison coefficient, or Poincare input is
introduced here.
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

/-- On the diagonal current-value specialization, the remote full-configuration
heat-bath projection is exactly integration of the observable after target-link
replacement against the literal fixed-right kernel-section one-link law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_diagonal_eq_kernelSectionSpatialLinkIntegral
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hf : StronglyMeasurable f) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
        H N hN beta hbeta C target source target
        (C source) (C target) f A =
      ∫ g, f (Function.update A target g)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
          H N hN beta hbeta C A target := by
  have hUpdate :
      Measurable
        (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
          Function.update A target g) :=
    measurable_update A
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel_apply]
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_apply_eq_map
      H N hN beta hbeta C target source target
      (C source) (C target) A]
  calc
    (∫ D, f D
      ∂Measure.map
        (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
          Function.update A target g)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta C target source target
          (C source) (C target) A)) =
      ∫ g, f (Function.update A target g)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta C target source target
          (C source) (C target) A := by
      exact
        MeasureTheory.integral_map hUpdate.aemeasurable hf.aestronglyMeasurable
    _ =
      ∫ g, f (Function.update A target g)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
          H N hN beta hbeta C A target := by
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_diagonal_eq_kernelSectionSpatialLinkNormalizedMeasure
          H N hN beta hbeta C A target source]

/-- Haar-almost-everywhere in the genuine split outer coordinates, the
canonical genuine fiber mean is the diagonal remote kernel-section one-link
projection of the right observable. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean_ae_eq_diagonalRemoteKernelSectionProjection
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) :
    ∀ᵐ left ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
      ∀ᵐ retained ∂(Measure.pi
        (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
          normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))),
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean
            H N hN beta hbeta target F (left, retained) =
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
            H N hN beta hbeta left target source target
            (left source) (left target)
            (fun D => F (left, D))
            (periodicHypercubicEvenSpecialUnitarySpatialSliceRightFromOffTarget
              H N target retained) := by
  have hMean :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean_ae_eq_kernelSectionSpatialLinkIntegral
      H N hN beta hbeta target F hF
  filter_upwards [hMean] with left hleft
  filter_upwards [hleft] with retained hmean
  let right :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceRightFromOffTarget
      H N target retained
  let f :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    fun D => F (left, D)
  have hf : StronglyMeasurable f := by
    dsimp [f]
    exact hF.comp_measurable (measurable_const.prodMk measurable_id)
  have hProj :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_diagonal_eq_kernelSectionSpatialLinkIntegral
      H N hN beta hbeta left right target source f hf
  have hSection :
      (fun g =>
        periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
          H N target F left retained g) =
      (fun g => f (Function.update right target g)) := by
    funext g
    unfold periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
    dsimp [f, right]
    rw [←
      periodicHypercubicEvenSpecialUnitarySpatialSliceOffTargetRestriction_rightFromOffTarget
        H N target retained]
    rw [
      periodicHypercubicEvenSpatialSliceTargetOffTarget_symm_offTargetRestriction_eq_update]
    simp
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean
        H N hN beta hbeta target F (left, retained) =
      ∫ g,
        periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
          H N target F left retained g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
          H N hN beta hbeta left right target := by
      simpa [right] using hmean
    _ =
      ∫ g, f (Function.update right target g)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
          H N hN beta hbeta left right target := by
      rw [hSection]
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
        H N hN beta hbeta left target source target
        (left source) (left target) f right := hProj.symm
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
        H N hN beta hbeta left target source target
        (left source) (left target)
        (fun D => F (left, D))
        (periodicHypercubicEvenSpecialUnitarySpatialSliceRightFromOffTarget
          H N target retained) := by
      rfl

/-- In the same outer coordinates, the canonical genuine centered residual is
exactly the existing diagonal remote kernel-section fluctuation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean_residual_ae_eq_diagonalRemoteKernelSectionFluctuation
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) :
    ∀ᵐ left ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
      ∀ᵐ retained ∂(Measure.pi
        (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
          normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))),
        let right :=
          periodicHypercubicEvenSpecialUnitarySpatialSliceRightFromOffTarget
            H N target retained
        F (left, right) -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean
              H N hN beta hbeta target F (left, retained) =
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
            H N hN beta hbeta left target source target
            (left source) (left target)
            (fun D => F (left, D)) right := by
  have hMean :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean_ae_eq_diagonalRemoteKernelSectionProjection
      H N hN beta hbeta target source F hF
  filter_upwards [hMean] with left hleft
  filter_upwards [hleft] with retained hmean
  dsimp
  rw [hmean]
  rfl

end

end MathlibAnalytic
end MGAP4D
