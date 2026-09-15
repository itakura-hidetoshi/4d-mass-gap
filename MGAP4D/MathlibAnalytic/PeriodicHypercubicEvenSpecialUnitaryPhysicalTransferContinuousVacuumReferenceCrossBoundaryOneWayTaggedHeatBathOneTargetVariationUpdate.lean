import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCrossBoundaryOneWayTaggedHeatBathVariationKernelBound
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance referenceCrossBoundaryOneWayTaggedHeatBathOneTargetVariationUpdateSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance referenceCrossBoundaryOneWayTaggedHeatBathOneTargetVariationUpdateSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance referenceCrossBoundaryOneWayTaggedHeatBathOneTargetVariationUpdateSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance referenceCrossBoundaryOneWayTaggedHeatBathOneTargetVariationUpdateSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance referenceCrossBoundaryOneWayTaggedHeatBathOneTargetVariationUpdateSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance referenceCrossBoundaryOneWayTaggedHeatBathOneTargetVariationUpdateSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Lift a physical left-fiber variation profile to the tagged carrier, with no
right-coordinate variation inserted.  This is a bookkeeping profile, not a
claim that any unrepresented physical reverse influence vanishes. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation
    (H : ℕ)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ) :
    Sum
        (PeriodicHypercubicEvenSpatialSliceLink H)
        (PeriodicHypercubicEvenSpatialSliceLink H) → ℝ
  | Sum.inl fiber => variation fiber
  | Sum.inr _source => 0

/-- The represented continuous C5 one-link heat-bath variation estimate is one
literal target-update step of the generic one-way tagged kernel when the input
observable carries variation only on the physical left fibers.

Only the represented left-target/right-source block is used.  No physical
meaning is assigned to the carrier's structurally-zero reverse or same-side
blocks. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTagged_oneLinkHeatBath_fiberVariation_influence_le_oneTargetUpdatedVariation
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k₁ k₂ g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hF : StronglyMeasurable F)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (hFiberVariation :
      ∀ g h : Matrix.specialUnitaryGroup (Fin N) ℂ,
        |F (Function.update A fiber g) - F (Function.update A fiber h)| ≤
          variation fiber) :
    |(∫ C, F C
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
          H N hN beta hbeta B target source fiber k₁ g₂ A) -
      (∫ C, F C
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
          H N hN beta hbeta B target source fiber k₂ g₂ A)| ≤
      finiteInfluenceKernelUpdatedVariation
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData
          H beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation
          H variation)
        (Sum.inl fiber)
        (Sum.inr source) := by
  rfl

end

end MathlibAnalytic
end MGAP4D
