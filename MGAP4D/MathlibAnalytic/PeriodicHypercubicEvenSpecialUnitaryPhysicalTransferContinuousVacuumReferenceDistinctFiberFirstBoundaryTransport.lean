import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceDistinctFiberOffFiberVariationPropagation
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCrossBoundaryHeatBathDistinctFiberTransportCriterion
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance referenceDistinctFiberFirstBoundaryTransportSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- RED probe: the explicit normalized literal-C5 off-fiber coefficient
discharges the `hFirstBoundary` obligation of the distinct-fiber two-step
transport criterion. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiber_twoStepHeatBath_firstBoundary_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber₁ fiber₂ : PeriodicHypercubicEvenSpatialSliceLink H)
    (hDistinct : fiber₁ ≠ fiber₂)
    (k₁ k₂ g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hF : StronglyMeasurable F)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (hVariation :
      ∀ (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
        |F (Function.update C e u) - F (Function.update C e v)| ≤ variation e) :
    |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTwoStepExpectation
          H N hN beta hbeta B target source fiber₁ fiber₂ k₁ k₁ g₂ A F -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTwoStepExpectation
          H N hN beta hbeta B target source fiber₁ fiber₂ k₂ k₁ g₂ A F| ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta fiber₁ source *
        (variation fiber₁ +
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
            beta * variation fiber₂) := by
  rfl

end

end MathlibAnalytic
end MGAP4D
