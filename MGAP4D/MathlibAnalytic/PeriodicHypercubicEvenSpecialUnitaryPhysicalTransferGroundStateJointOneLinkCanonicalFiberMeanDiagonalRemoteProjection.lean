import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkCanonicalFiberMeanKernelSectionIntegral
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferDiagonalProjectionKernelSectionIntegral
import Mathlib.Tactic

/-!
# Canonical genuine fiber mean equals the diagonal remote projection

PR #4758 identifies the canonical genuine target-fiber mean with the literal
fixed-right kernel-section one-link integral, Haar-almost-everywhere in the
retained outer context.

PR #4760 identifies the diagonal remote heat-bath projection pointwise with
that same kernel-section one-link integral.

This file glues the two presentations.  The resulting canonical centered
residual is exactly the already-defined diagonal remote kernel-section
fluctuation.  No comparison coefficient, remote-response estimate, or
Poincare input is introduced.
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
  let X :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    fun D => F (left, D)
  have hX : StronglyMeasurable X := by
    dsimp [X]
    exact hF.comp_measurable (measurable_const.prodMk measurable_id)
  have hSection :
      (fun g =>
        periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
          H N target F left retained g) =
      (fun g => X (Function.update right target g)) := by
    funext g
    unfold periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
    dsimp [X, right]
    rw [←
      periodicHypercubicEvenSpecialUnitarySpatialSliceOffTargetRestriction_rightFromOffTarget
        H N target retained]
    rw [
      periodicHypercubicEvenSpatialSliceTargetOffTarget_symm_offTargetRestriction_eq_update]
    simp
  have hProj :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_diagonal_eq_kernelSectionSpatialLinkIntegral
      H N hN beta hbeta left right target source X hX
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
      ∫ g, X (Function.update right target g)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
          H N hN beta hbeta left right target := by
      rw [hSection]
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
        H N hN beta hbeta left target source target
        (left source) (left target) X right := hProj.symm
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
        F
            (left,
              periodicHypercubicEvenSpecialUnitarySpatialSliceRightFromOffTarget
                H N target retained) -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean
            H N hN beta hbeta target F (left, retained) =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
          H N hN beta hbeta left target source target
          (left source) (left target)
          (fun D => F (left, D))
          (periodicHypercubicEvenSpecialUnitarySpatialSliceRightFromOffTarget
            H N target retained) := by
  have hMean :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean_ae_eq_diagonalRemoteKernelSectionProjection
      H N hN beta hbeta target source F hF
  filter_upwards [hMean] with left hleft
  filter_upwards [hleft] with retained hmean
  rw [hmean]
  rfl

end

end MathlibAnalytic
end MGAP4D
