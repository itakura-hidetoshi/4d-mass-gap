import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCrossBoundaryHeatBathVariationRowOperator
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance referenceCrossBoundaryHeatBathTwoStepVariationPropagationSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance referenceCrossBoundaryHeatBathTwoStepVariationPropagationSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance referenceCrossBoundaryHeatBathTwoStepVariationPropagationSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance referenceCrossBoundaryHeatBathTwoStepVariationPropagationSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance referenceCrossBoundaryHeatBathTwoStepVariationPropagationSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance referenceCrossBoundaryHeatBathTwoStepVariationPropagationSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- First genuine two-step continuous C5 variation target: repeat the same
physical one-link heat-bath update twice and dominate the represented
right-source discrepancy by two applications of the existing tagged target
update.  This deliberately stays on one physical fiber, so it does not use any
carrier-scope zero as a theorem about unrepresented left-left physical
influence. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTagged_twoStepSameFiberHeatBath_fiberVariation_influence_le_twoTargetUpdatedVariation
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
        ∂((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
              H N hN beta hbeta B target source fiber k₁ g₂) ∘ₖ
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
              H N hN beta hbeta B target source fiber k₁ g₂)) A) -
      (∫ C, F C
        ∂((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
              H N hN beta hbeta B target source fiber k₂ g₂) ∘ₖ
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
              H N hN beta hbeta B target source fiber k₂ g₂)) A)| ≤
      finiteInfluenceKernelUpdatedVariation
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData
          H beta hbeta)
        (fun e =>
          finiteInfluenceKernelUpdatedVariation
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData
              H beta hbeta)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation
              H variation)
            (Sum.inl fiber)
            e)
        (Sum.inl fiber)
        (Sum.inr source) := by
  rfl

end

end MathlibAnalytic
end MGAP4D
