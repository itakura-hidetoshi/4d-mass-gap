import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceOneLinkFiber
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumGroundStateKernelSectionLeftFiberNormalizedMeasure
import Mathlib.Tactic

/-!
# Diagonal reference one-link fiber equals the kernel-section one-link law

For a fixed right boundary `C`, specialize the continuous-vacuum reference
construction by inserting into the source and distinguished target slots the
values already present in `C`.

Then both updates restore `C`.  Moreover the right-target local factor at the
already-present target value is exactly one.  Therefore the literal reference
one-link fiber weight is pointwise the fixed-right kernel-section one-link
weight, and the two normalized Haar laws agree exactly.

No remote-separation hypothesis, comparison constant, or conditional-law
argument is required.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

attribute [local instance]
  continuousVacuumReferenceOneLinkFiberSpecialUnitaryIsTopologicalGroup
  continuousVacuumReferenceOneLinkFiberSpecialUnitaryCompactSpace
  continuousVacuumReferenceOneLinkFiberSpecialUnitarySecondCountableTopology
  continuousVacuumReferenceOneLinkFiberSpecialUnitaryMeasurableSpace
  continuousVacuumReferenceOneLinkFiberSpecialUnitaryBorelSpace
  continuousVacuumReferenceOneLinkFiberSpatialLinkFintype

/-- At the diagonal current values, the literal reference one-link fiber
weight is exactly the fixed-right kernel-section one-link weight. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_diagonal_eq_kernelSectionSpatialLinkWeight
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
        H N hN beta hbeta C target source target
        (C source) (C target) A g =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkWeight
        H N hN beta hbeta C A target g := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkWeight
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
  have hSource :
      Function.update C source (C source) = C := by
    simp
  rw [hSource]
  have hTargetFactor :
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta (Function.update A target g) C target (C target) = 1 := by
    unfold
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
    simp
  rw [hTargetFactor]
  ring

/-- Consequently the normalized literal reference fiber law is exactly the
normalized fixed-right kernel-section one-link law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_diagonal_eq_kernelSectionSpatialLinkNormalizedMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta C target source target
        (C source) (C target) A =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
        H N hN beta hbeta C A target := by
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
    realIntegralWeightedProbabilityMeasure
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkENNRealWeight
  change
    doobWeightedMeasure μ
        (fun g =>
          ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
              H N hN beta hbeta C target source target
              (C source) (C target) A g)) =
      doobWeightedMeasure μ
        (fun g =>
          ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkWeight
              H N hN beta hbeta C A target g))
  apply congrArg (doobWeightedMeasure μ)
  funext g
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_diagonal_eq_kernelSectionSpatialLinkWeight
      H N hN beta hbeta C A target source g]

end

end MathlibAnalytic
end MGAP4D
