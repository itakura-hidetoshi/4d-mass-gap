import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkCanonicalFiberVarianceCenteredResidual
import Mathlib.Tactic

/-!
# Exact centered-residual presentation of canonical fiber variance

The canonical genuine split kernel agrees outer-almost-everywhere with the
historical normalized split fiber.  On the canonical kernel, the canonical
fiber mean is exactly the center defining Mathlib's extended variance.

Consequently the weighted canonical fiber-variance functional is not merely
bounded by a centered residual: it is exactly the genuine centered-residual
functional when the center is the canonical fiber mean.

This is a law/presentation identity only.  No comparison constant,
source/target exchange, or Poincare input is introduced.
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

/-- The canonical weighted one-link fiber variance is exactly the genuine
centered-residual functional centered at the canonical fiber mean. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional_eq_centeredResidual_canonicalFiberMean
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
        H N hN beta hbeta target F =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkBoundedCoreCenteredResidualFunctional
        H N hN beta hbeta target F
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean
          H N hN beta hbeta target F) := by
  let μLeft :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let μOff :=
    Measure.pi
      (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
        normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
  let eval :=
    periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target
  let coord :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitContextTargetMeasurableEquiv
      H N target
  have hcanon :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel_ae_eq_normalizedFiber
      H N hN beta hbeta target
  have hcanonNested :
      ∀ᵐ left ∂μLeft,
        ∀ᵐ retained ∂μOff,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel
              H N hN beta hbeta target (left, retained) =
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
              H N hN beta hbeta left target retained := by
    simpa [μLeft, μOff] using (Measure.ae_ae_of_ae_prod hcanon)
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkBoundedCoreCenteredResidualFunctional
  apply lintegral_congr_ae
  filter_upwards [hcanonNested] with left hleft
  apply lintegral_congr_ae
  filter_upwards [hleft] with retained hkernel
  let X :=
    fun targetCfg =>
      periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
        H N target F left retained (eval targetCfg)
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
  have hEq :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean_centeredSquaredResidual_eq_evariance
      H N hN beta hbeta target F (left, retained)
  rw [hCoord] at hEq
  have hEqHistorical :
      doobCenteredSquaredResidual
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
            H N hN beta hbeta left target retained)
          X
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean
            H N hN beta hbeta target F (left, retained)) =
        evariance X
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel
            H N hN beta hbeta target (left, retained)) := by
    calc
      doobCenteredSquaredResidual
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
            H N hN beta hbeta left target retained)
          X
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean
            H N hN beta hbeta target F (left, retained)) =
        doobCenteredSquaredResidual
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel
            H N hN beta hbeta target (left, retained))
          X
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean
            H N hN beta hbeta target F (left, retained)) := by
          rw [hkernel]
      _ =
        evariance X
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel
            H N hN beta hbeta target (left, retained)) := hEq
  exact congrArg
    (fun v : ℝ≥0∞ =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass
          H N hN beta hbeta left target retained * v)
    hEqHistorical.symm

end

end MathlibAnalytic
end MGAP4D
