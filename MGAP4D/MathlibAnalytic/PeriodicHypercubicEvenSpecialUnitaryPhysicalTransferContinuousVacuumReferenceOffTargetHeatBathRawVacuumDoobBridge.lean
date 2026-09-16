import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceOffTargetFiberKernelSectionBridge
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCrossBoundaryHeatBathRow
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance referenceOffTargetHeatBathRawVacuumDoobSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance referenceOffTargetHeatBathRawVacuumDoobSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance referenceOffTargetHeatBathRawVacuumDoobSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance referenceOffTargetHeatBathRawVacuumDoobSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance referenceOffTargetHeatBathRawVacuumDoobSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The older literal reference-fiber probability law and the newer named
normalized ENNReal fiber law are exactly the same measure.  This is only a
normalization-definition bridge; it introduces no conditional-probability
claim. -/
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
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
    realIntegralWeightedProbabilityMeasure
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSpatialLinkFiberNormalizedMeasure
  apply congrArg
    (fun w : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ≥0∞ =>
      doobWeightedMeasure
        (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) w)
  funext g
  simp [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSpatialLinkFiberENNRealWeight,
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink]

/-- Away from the distinguished target, the literal reference-fiber
probability law used by the existing heat-bath machinery is exactly a
continuous-vacuum Doob reweighting of the raw one-slab local Boltzmann law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_eq_raw_vacuum_doob_of_ne_target
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (hFiberTarget : fiber ≠ target)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta B target source fiber k g₂ A =
      doobWeightedMeasure
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabKernelSectionRawSpatialLinkMeasure
          H N beta (Function.update B source k) A fiber)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberWeight
          H N hN beta hbeta A fiber) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_eq_spatialLinkFiberNormalizedMeasure]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSpatialLinkFiberNormalizedMeasure_eq_raw_vacuum_doob_of_ne_target
      H N hN beta hbeta B target source fiber hFiberTarget k g₂ A

/-- The existing measurable one-link conditional kernel therefore has the same
raw-one-slab / vacuum-Doob representation at every off-target fiber. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel_apply_eq_raw_vacuum_doob_of_ne_target
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (hFiberTarget : fiber ≠ target)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel
        H N hN beta hbeta B target source fiber k g₂ A =
      doobWeightedMeasure
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabKernelSectionRawSpatialLinkMeasure
          H N beta (Function.update B source k) A fiber)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberWeight
          H N hN beta hbeta A fiber) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel_apply]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_eq_raw_vacuum_doob_of_ne_target
      H N hN beta hbeta B target source fiber hFiberTarget k g₂ A

/-- Sampling and reinsertion preserve the exact representation: an off-target
C5 heat-bath update is the pushforward of the raw one-slab local law after
continuous-vacuum Doob reweighting. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_apply_eq_map_raw_vacuum_doob_of_ne_target
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (hFiberTarget : fiber ≠ target)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
        H N hN beta hbeta B target source fiber k g₂ A =
      (doobWeightedMeasure
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabKernelSectionRawSpatialLinkMeasure
          H N beta (Function.update B source k) A fiber)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberWeight
          H N hN beta hbeta A fiber)).map
        (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
          Function.update A fiber g) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_apply_eq_map_fiberProbabilityMeasure,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_eq_raw_vacuum_doob_of_ne_target
      H N hN beta hbeta B target source fiber hFiberTarget k g₂ A]

end

end MathlibAnalytic
end MGAP4D
