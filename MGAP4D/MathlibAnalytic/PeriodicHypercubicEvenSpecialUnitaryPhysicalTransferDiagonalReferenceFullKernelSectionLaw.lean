import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairUpdatedVarianceReferenceResidual
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferDiagonalReferenceFiberKernelSectionLaw
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFullKernelSectionBridge
import Mathlib.Tactic

/-!
# Diagonal reference law equals the full fixed-right kernel-section law

PR #4759 proves the diagonal law identity only for the distinguished reference
target fiber.  The current source-pair variance chain needs an arbitrary
response target fiber.

At current-value parameters

  k  = C(referenceSource),
  g₂ = C(referenceTarget),

both stored right-boundary updates are identities and the reference target
local factor is exactly one.  Therefore:

* the complete normalized reference law is the fixed-right kernel-section law;
* every literal one-link reference fiber, not only the referenceTarget fiber,
  is the corresponding fixed-right kernel-section one-link law;
* the reference heat-bath projection on any resampled fiber is exactly the
  kernel-section one-link expectation.

No remote-separation hypothesis, comparison coefficient, or Poincare input is
used.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance diagonalReferenceFullKernelSectionSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance diagonalReferenceFullKernelSectionSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance diagonalReferenceFullKernelSectionSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance diagonalReferenceFullKernelSectionSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance diagonalReferenceFullKernelSectionSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance diagonalReferenceFullKernelSectionSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- At current-value parameters the complete continuous-vacuum reference
weight is exactly the fixed-right kernel-section continuous weight. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight_diagonalCurrentValues_eq_kernelSectionContinuousWeight
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (referenceTarget referenceSource :
      PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
        H N hN beta hbeta C referenceTarget referenceSource
        (C referenceSource) (C referenceTarget) A =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
        H N hN beta hbeta C A := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
  have hSource :
      Function.update C referenceSource (C referenceSource) = C := by
    simp
  rw [hSource]
  have hTargetFactor :
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A C referenceTarget (C referenceTarget) = 1 := by
    unfold
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
    simp
  rw [hTargetFactor]
  ring

/-- Consequently the complete normalized diagonal reference probability law is
exactly the fixed-right continuous kernel-section probability law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_diagonalCurrentValues_eq_kernelSection
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (referenceTarget referenceSource :
      PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta C referenceTarget referenceSource
        (C referenceSource) (C referenceTarget) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta C := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
  apply congrArg
    (realIntegralWeightedProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
  funext A
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight_diagonalCurrentValues_eq_kernelSectionContinuousWeight
      H N hN beta hbeta C A referenceTarget referenceSource

/-- The diagonal current-value fiber law agrees with the kernel-section law on
an arbitrary resampled fiber.  This generalizes PR #4759 beyond the
referenceTarget fiber. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_diagonalCurrentValues_eq_kernelSectionSpatialLinkNormalizedMeasure
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (referenceTarget referenceSource fiber :
      PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta C referenceTarget referenceSource fiber
        (C referenceSource) (C referenceTarget) A =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
        H N hN beta hbeta C A fiber := by
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
              H N hN beta hbeta C referenceTarget referenceSource fiber
              (C referenceSource) (C referenceTarget) A g)) =
      doobWeightedMeasure μ
        (fun g =>
          ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkWeight
              H N hN beta hbeta C A fiber g))
  apply congrArg (doobWeightedMeasure μ)
  funext g
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkWeight
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
  have hSource :
      Function.update C referenceSource (C referenceSource) = C := by
    simp
  rw [hSource]
  have hTargetFactor :
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta (Function.update A fiber g) C
          referenceTarget (C referenceTarget) = 1 := by
    unfold
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
    simp
  rw [hTargetFactor]
  ring

/-- At diagonal current values, the reference heat-bath projection on any
fiber is exactly the fixed-right kernel-section one-link expectation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection_diagonalCurrentValues_eq_kernelSectionSpatialLinkIntegral
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (referenceTarget referenceSource fiber :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hX : StronglyMeasurable X) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection
        H N hN beta hbeta C referenceTarget referenceSource fiber
        (C referenceSource) (C referenceTarget) X A =
      ∫ g,
        X (Function.update A fiber g)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
          H N hN beta hbeta C A fiber := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection_eq_fiberIntegral
      H N hN beta hbeta C referenceTarget referenceSource fiber
      (C referenceSource) (C referenceTarget) X hX A,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_diagonalCurrentValues_eq_kernelSectionSpatialLinkNormalizedMeasure
      H N hN beta hbeta C A referenceTarget referenceSource fiber]

end

end MGAP4D.MathlibAnalytic
