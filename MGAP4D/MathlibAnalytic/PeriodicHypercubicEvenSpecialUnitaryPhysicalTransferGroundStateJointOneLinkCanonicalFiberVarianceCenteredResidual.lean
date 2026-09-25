import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkCanonicalFiberVariance
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkBoundedCoreCondExp
import Mathlib.Tactic

/-!
# Canonical fiber variance to the genuine one-link centered residual

PR #4752 proves fiberwise that the canonical genuine target-link mean minimizes
the squared residual on each canonical Markov fiber.  The canonical kernel from
PR #4750 agrees outer-almost-everywhere with the historical normalized split
fiber.

This file integrates that coefficient-one fiber inequality against the exact
ground-state target-fiber mass.  The result places the canonical weighted fiber
variance below the already-established genuine one-link centered-residual
functional.

The source file's exact local typeclass bundle is reused because the hidden
terms carried by `Measure.pi` are part of the elaborated measure expression.
No equivalent-but-distinct wrapper instances are introduced.
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

/-- Outer-context average of the exact canonical genuine one-link fiber
variance, weighted by the historical exact target-fiber mass. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ) : ℝ≥0∞ :=
  ∫⁻ left,
    ∫⁻ retained,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass
            H N hN beta hbeta left target retained *
        evariance
          (fun targetCfg =>
            periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
              H N target F left retained
              (periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
                (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target targetCfg))
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel
            H N hN beta hbeta target (left, retained))
      ∂(Measure.pi
        (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
          normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
    ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)

/-- The canonical weighted fiber variance is bounded with coefficient one by
the genuine one-link centered-residual functional at any strongly measurable
outer center. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional_le_centeredResidual
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (C :
      PeriodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContext
        H N target → ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
        H N hN beta hbeta target F ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkBoundedCoreCenteredResidualFunctional
        H N hN beta hbeta target F C := by
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
    simpa only [μLeft, μOff] using hcanon.prod_right_ae
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkBoundedCoreCenteredResidualFunctional
  refine lintegral_mono_ae ?_
  filter_upwards [hcanonNested] with left hleft
  refine lintegral_mono_ae ?_
  filter_upwards [hleft] with retained hkernel
  let X :=
    fun targetCfg =>
      periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
        H N target F left retained (eval targetCfg)
  have hCoord :
      (fun targetCfg =>
        F (coord ((left, retained), targetCfg))) = X := by
    funext targetCfg
    simp [X, coord, eval,
      periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection]
  have hMin :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean_centeredSquaredResidual_le
      H N hN beta hbeta target F hF bound hbound
      (left, retained) (C (left, retained))
  have hEq :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean_centeredSquaredResidual_eq_evariance
      H N hN beta hbeta target F (left, retained)
  have hVarCanonical :
      evariance X
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel
            H N hN beta hbeta target (left, retained)) ≤
        doobCenteredSquaredResidual
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel
            H N hN beta hbeta target (left, retained))
          X
          (C (left, retained)) := by
    rw [← hCoord]
    calc
      evariance
          (fun targetCfg => F (coord ((left, retained), targetCfg)))
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel
            H N hN beta hbeta target (left, retained)) =
        doobCenteredSquaredResidual
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel
            H N hN beta hbeta target (left, retained))
          (fun targetCfg => F (coord ((left, retained), targetCfg)))
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean
            H N hN beta hbeta target F (left, retained)) := hEq.symm
      _ ≤
        doobCenteredSquaredResidual
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel
            H N hN beta hbeta target (left, retained))
          (fun targetCfg => F (coord ((left, retained), targetCfg)))
          (C (left, retained)) := hMin
  have hVarHistorical := hVarCanonical
  rw [hkernel] at hVarHistorical
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass
          H N hN beta hbeta left target retained *
        evariance X
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel
            H N hN beta hbeta target (left, retained)) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass
          H N hN beta hbeta left target retained *
        evariance X
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
            H N hN beta hbeta left target retained) := by
      rw [hkernel]
    _ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass
          H N hN beta hbeta left target retained *
        doobCenteredSquaredResidual
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
            H N hN beta hbeta left target retained)
          X
          (C (left, retained)) :=
      mul_le_mul_left' hVarHistorical
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass
          H N hN beta hbeta left target retained)

end

end MathlibAnalytic
end MGAP4D
