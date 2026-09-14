import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceTwoSourceKernelDifference
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabRightTargetLocalFactorBounds
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The difference of two literal C5 source-sensitive one-slab kernels factors
through the difference of the exact right-boundary source-local Boltzmann
factors, times the unmodified one-slab kernel.

This is still a pointwise identity in the selected left fiber variable `g` and
uses no distance estimate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkSourceKernel_sub_eq_sourceLocalFactorDifference_mul_baseKernel
    (H N : ℕ)
    (beta : ℝ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k₁ k₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkSourceKernel
          H N beta B source fiber k₁ A g -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkSourceKernel
          H N beta B source fiber k₂ A g =
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
            H N A fiber g)
          B source k₁ -
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
            H N A fiber g)
          B source k₂) *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
            H N A fiber g)
          B := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkSourceKernel
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_eq_localFactor_mul]
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_eq_localFactor_mul]
  ring

/-- If the right-boundary source link is distinct from the selected left fiber,
then the exact source-local Boltzmann factor is independent of the fiber value
`g`: the left boundary enters that factor only through its value at `source`.

This is stronger than a decay estimate: the entire source multiplier becomes a
fiber-independent scalar. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_continuousVacuumReplaceLink_eq_of_source_ne_fiber
    (H N : ℕ)
    (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hNe : source ≠ fiber) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
        H N beta
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
          H N A fiber g)
        B source k =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
        H N beta A B source k := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
  rw [periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_of_ne
    H N A fiber source g hNe]

/-- Consequently, for distinct source and fiber, the literal source-kernel
difference is a fiber-independent scalar difference times one common base
one-slab kernel.

All `g`-dependence is confined to the common base kernel. This is the exact
interface for testing whether source normalization cancels completely before
any distance-sensitive estimate is introduced. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkSourceKernel_sub_eq_distinctSourceScalarDifference_mul_baseKernel
    (H N : ℕ)
    (beta : ℝ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k₁ k₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hNe : source ≠ fiber) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkSourceKernel
          H N beta B source fiber k₁ A g -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkSourceKernel
          H N beta B source fiber k₂ A g =
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B source k₁ -
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B source k₂) *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
            H N A fiber g)
          B := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkSourceKernel_sub_eq_sourceLocalFactorDifference_mul_baseKernel]
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_continuousVacuumReplaceLink_eq_of_source_ne_fiber
    H N beta A B source fiber k₁ g hNe]
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_continuousVacuumReplaceLink_eq_of_source_ne_fiber
    H N beta A B source fiber k₂ g hNe]

end

end MathlibAnalytic
end MGAP4D
