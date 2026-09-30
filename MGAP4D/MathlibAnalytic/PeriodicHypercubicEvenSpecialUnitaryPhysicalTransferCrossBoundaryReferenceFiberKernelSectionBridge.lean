import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceOffTargetFiberKernelSectionBridge
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceOneLinkFiber
import Mathlib.Tactic

/-!
# Cross-boundary reference fiber as an actual updated kernel-section fiber

The cross-boundary L2 comparison is stated for the literal continuous-vacuum
reference one-link probability measure. To use it in the genuine fixed-right
kernel-section hierarchy we identify that law exactly.

When the distinguished target value is the actual current value B target,
the reference target-local factor is exactly one on the target fiber itself.
For fibers different from the distinguished target, the existing off-target
normalization theorem already removes that factor. Combining the two cases
gives, for every source and every left resampled fiber,

  referenceFiber(B, source := k, target := B target; fiber)
    =
  kernelSectionFiber(B[source <- k]; fiber).

No Harnack loss, no a.e. replacement, and no coefficient is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

local instance crossBoundaryReferenceFiberBridgeSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance crossBoundaryReferenceFiberBridgeSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance crossBoundaryReferenceFiberBridgeSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance crossBoundaryReferenceFiberBridgeSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance crossBoundaryReferenceFiberBridgeSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance crossBoundaryReferenceFiberBridgeSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The older literal one-link reference probability law and the later
SpatialLinkFiberNormalizedMeasure presentation are the same normalized Haar
density. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_eq_spatialLinkFiberNormalizedMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta B target source fiber k g₂ A =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSpatialLinkFiberNormalizedMeasure
        H N hN beta hbeta B target source k g₂ A fiber := by
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
    realIntegralWeightedProbabilityMeasure
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSpatialLinkFiberNormalizedMeasure
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSpatialLinkFiberENNRealWeight
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
  change
    doobWeightedMeasure μ
        (fun g =>
          ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
              H N hN beta hbeta B target source k g₂
              (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
                H N A fiber g))) =
      doobWeightedMeasure μ
        (fun g =>
          ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
              H N hN beta hbeta B target source k g₂
              (Function.update A fiber g)))
  apply congrArg (doobWeightedMeasure μ)
  funext g
  simp [periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink]

/-- On the distinguished target fiber itself, inserting the current target
value makes the target-local reference factor exactly one. The remaining
weight is exactly the kernel-section weight with the right source updated to k.
-/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_currentTarget_targetFiber_eq_kernelSection_sourceUpdate
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
        H N hN beta hbeta B target source target k (B target) A g =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkWeight
        H N hN beta hbeta (Function.update B source k) A target g := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkWeight
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
  have hTargetFactor :
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta (Function.update A target g) B target (B target) = 1 := by
    unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
    simp
  rw [hTargetFactor]
  ring

/-- Hence the normalized target fiber itself is exactly the actual
kernel-section target fiber for the source-updated right boundary. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_currentTarget_targetFiber_eq_kernelSection_sourceUpdate
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta B target source target k (B target) A =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
        H N hN beta hbeta (Function.update B source k) A target := by
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
              H N hN beta hbeta B target source target k (B target) A g)) =
      doobWeightedMeasure μ
        (fun g =>
          ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkWeight
              H N hN beta hbeta (Function.update B source k) A target g))
  apply congrArg (doobWeightedMeasure μ)
  funext g
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_currentTarget_targetFiber_eq_kernelSection_sourceUpdate
      H N hN beta hbeta B target source k A g]

/-- Uniform exact bridge for every resampled left fiber. Off the distinguished
target this is the existing constant-factor normalization theorem; on the
target it is the preceding current-target identity. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_currentTarget_eq_kernelSection_sourceUpdate
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta B target source fiber k (B target) A =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
        H N hN beta hbeta (Function.update B source k) A fiber := by
  by_cases hft : fiber = target
  · subst fiber
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_currentTarget_targetFiber_eq_kernelSection_sourceUpdate
        H N hN beta hbeta B target source k A
  · rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_eq_spatialLinkFiberNormalizedMeasure
        H N hN beta hbeta B target source fiber k (B target) A]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSpatialLinkFiberNormalizedMeasure_eq_kernelSection_of_ne_target
        H N hN beta hbeta B target source fiber hft k (B target) A

end

end MathlibAnalytic
end MGAP4D
