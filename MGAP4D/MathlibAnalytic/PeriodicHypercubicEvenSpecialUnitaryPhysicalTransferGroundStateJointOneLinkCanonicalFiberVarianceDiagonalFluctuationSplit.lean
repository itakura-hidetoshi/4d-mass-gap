import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkCanonicalFiberMeanDiagonalRemoteProjectionFiberwise
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkCanonicalFiberVarianceCenteredResidual
import Mathlib.Tactic

/-!
# Canonical fiber variance as split diagonal-fluctuation energy

PR #4764 upgrades the canonical-mean / diagonal-remote-projection identity to
every target-fiber value over almost every retained outer context.

This file inserts that pointwise fiber identity into the canonical fiber
variance functional.  At each outer context, the canonical mean is the exact
variance-minimizing center, so Mathlib's `evariance` is first rewritten as the
corresponding centered squared residual.  The residual is then replaced
pointwise by the diagonal remote kernel-section fluctuation from PR #4764.

The result is an exact split-coordinate energy identity.  No measure change,
comparison coefficient, response estimate, or Poincare input is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

attribute [local instance]
  groundStateJointOneLinkCenteredResidualSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkCenteredResidualSpecialUnitaryCompactSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkCenteredResidualSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitaryBorelSpace
  groundStateJointOneLinkCenteredResidualSpatialLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkUnique

/-- The canonical weighted fiber variance is exactly the split outer-context
average of the squared diagonal remote kernel-section fluctuation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional_eq_split_diagonalRemoteFluctuation_lintegral
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
        H N hN beta hbeta target F =
      ∫⁻ left,
        ∫⁻ retained,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass
                H N hN beta hbeta left target retained *
            (∫⁻ targetCfg,
              ENNReal.ofReal
                ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
                    H N hN beta hbeta left target source target
                    (left source) (left target)
                    (fun D => F (left, D))
                    ((periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
                      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target).symm
                      (targetCfg, retained))) ^ 2)
              ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel
                H N hN beta hbeta target (left, retained))
          ∂(Measure.pi
            (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
              normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
        ∂periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N := by
  let eval :=
    periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target
  let coord :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitContextTargetMeasurableEquiv
      H N target
  have hResidual :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean_residual_ae_eq_diagonalRemoteKernelSectionFluctuation_fiberwise
      H N hN beta hbeta target source F hF
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
  apply lintegral_congr_ae
  filter_upwards [hResidual] with left hleft
  apply lintegral_congr_ae
  filter_upwards [hleft] with retained hres
  let X :=
    fun targetCfg =>
      periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
        H N target F left retained (eval targetCfg)
  let κ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel
      H N hN beta hbeta target (left, retained)
  have hCoord :
      (fun targetCfg =>
        F (coord ((left, retained), targetCfg))) = X := by
    funext targetCfg
    change
      F
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitContextTargetMeasurableEquiv
            H N target ((left, retained), targetCfg)) =
        periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
          H N target F left retained (eval targetCfg)
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitContextTargetMeasurableEquiv_apply]
    unfold periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
    rw [eval.symm_apply_apply]
  have hVar :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean_centeredSquaredResidual_eq_evariance
      H N hN beta hbeta target F (left, retained)
  rw [hCoord] at hVar
  have hInner :
      evariance X κ =
        ∫⁻ targetCfg,
          ENNReal.ofReal
            ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
                H N hN beta hbeta left target source target
                (left source) (left target)
                (fun D => F (left, D))
                ((periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
                  (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target).symm
                  (targetCfg, retained))) ^ 2)
          ∂κ := by
    calc
      evariance X κ =
        doobCenteredSquaredResidual κ X
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean
            H N hN beta hbeta target F (left, retained)) := hVar.symm
      _ =
        ∫⁻ targetCfg,
          ENNReal.ofReal
            ((X targetCfg -
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean
                  H N hN beta hbeta target F (left, retained)) ^ 2)
          ∂κ := by
        rfl
      _ =
        ∫⁻ targetCfg,
          ENNReal.ofReal
            ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
                H N hN beta hbeta left target source target
                (left source) (left target)
                (fun D => F (left, D))
                ((periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
                  (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target).symm
                  (targetCfg, retained))) ^ 2)
          ∂κ := by
        apply lintegral_congr
        intro targetCfg
        have hX :
            X targetCfg =
              F
                (left,
                  (periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
                    (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target).symm
                    (targetCfg, retained)) := by
          dsimp [X]
          unfold periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
          rw [eval.symm_apply_apply]
        rw [hX, hres targetCfg]
  change
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass
          H N hN beta hbeta left target retained *
        evariance X κ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass
          H N hN beta hbeta left target retained *
        (∫⁻ targetCfg,
          ENNReal.ofReal
            ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
                H N hN beta hbeta left target source target
                (left source) (left target)
                (fun D => F (left, D))
                ((periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
                  (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target).symm
                  (targetCfg, retained))) ^ 2)
          ∂κ)
  rw [hInner]

end

end MathlibAnalytic
end MGAP4D
