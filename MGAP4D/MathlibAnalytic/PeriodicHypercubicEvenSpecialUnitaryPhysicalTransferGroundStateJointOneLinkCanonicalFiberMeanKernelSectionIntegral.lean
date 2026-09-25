import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkCanonicalFiberMean
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateKernelSectionGenuineOneLinkFiberBridge
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkBoundedCoreCondExp
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Tactic

/-!
# Canonical genuine fiber mean in kernel-section one-link coordinates

PR #4750 fixes an integrand-independent canonical split target-link Markov
kernel and its measurable fiber mean.  PR #4747 identifies the historical
split target fiber, after evaluation of the singleton target coordinate, with
the literal one-link law inside the corresponding fixed-right kernel section.

This file combines those two facts.  Haar-almost-everywhere in the retained
outer context, the canonical genuine fiber mean is exactly the ordinary
one-link integral of the concrete section against the literal normalized
kernel-section fiber law.

This is a coordinate/law identification only.  No remote-geometry hypothesis,
comparison coefficient, or Poincare estimate is introduced.
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

/-- Almost everywhere in the genuine split outer coordinates, the canonical
fiber mean is the literal one-link kernel-section expectation of the concrete
section. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean_ae_eq_kernelSectionSpatialLinkIntegral
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
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
          ∫ g,
            periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
              H N target F left retained g
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
              H N hN beta hbeta left
              (periodicHypercubicEvenSpecialUnitarySpatialSliceRightFromOffTarget
                H N target retained) target := by
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
  have hmap :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure_ae_map_eq_kernelSectionContinuousSpatialLinkNormalizedMeasure
      H N hN beta hbeta target
  filter_upwards [hcanonNested, hmap] with left hcanonLeft hmapLeft
  filter_upwards [hcanonLeft, hmapLeft] with retained hkernel hmapRetained
  let X :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
      H N target F left retained
  have hX : StronglyMeasurable X := by
    simpa [X] using
      periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection_stronglyMeasurable
        H N target F hF left retained
  have hCoord :
      (fun targetCfg =>
        F (coord ((left, retained), targetCfg))) =
      (fun targetCfg => X (eval targetCfg)) := by
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
  change
    (∫ targetCfg,
      F (coord ((left, retained), targetCfg))
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel
        H N hN beta hbeta target (left, retained)) =
      ∫ g, X g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
          H N hN beta hbeta left
          (periodicHypercubicEvenSpecialUnitarySpatialSliceRightFromOffTarget
            H N target retained) target
  rw [hkernel, hCoord]
  calc
    (∫ targetCfg, X (eval targetCfg)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
        H N hN beta hbeta left target retained) =
      ∫ g, X g
        ∂Measure.map eval
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
            H N hN beta hbeta left target retained) := by
      symm
      exact MeasureTheory.integral_map_of_stronglyMeasurable eval.measurable hX
    _ =
      ∫ g, X g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
          H N hN beta hbeta left
          (periodicHypercubicEvenSpecialUnitarySpatialSliceRightFromOffTarget
            H N target retained) target := by
      rw [hmapRetained]

end

end MathlibAnalytic
end MGAP4D
