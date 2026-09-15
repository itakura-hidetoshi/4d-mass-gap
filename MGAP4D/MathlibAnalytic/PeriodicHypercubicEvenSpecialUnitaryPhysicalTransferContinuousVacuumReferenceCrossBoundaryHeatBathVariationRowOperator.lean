import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCrossBoundaryOneWayTaggedHeatBathOneTargetVariationUpdate
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCrossBoundaryInfluenceOperator
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

local instance referenceCrossBoundaryHeatBathVariationRowOperatorSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance referenceCrossBoundaryHeatBathVariationRowOperatorSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance referenceCrossBoundaryHeatBathVariationRowOperatorSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance referenceCrossBoundaryHeatBathVariationRowOperatorSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance referenceCrossBoundaryHeatBathVariationRowOperatorSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance referenceCrossBoundaryHeatBathVariationRowOperatorSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The full represented right-source row of the continuous C5 one-link
heat-bath update is controlled by the already-defined cross-boundary influence
operator acting on the physical left-fiber variation profile.

This is still a one-link statement.  It does not identify the generic tagged
random-scan iterate with a physical continuous random-scan chain and does not
assign physical meaning to structurally-zero reverse carrier blocks. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_fiberVariation_influence_rowSum_le_operator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k₁ k₂ :
      PeriodicHypercubicEvenSpatialSliceLink H →
        Matrix.specialUnitaryGroup (Fin N) ℂ)
    (g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hF : StronglyMeasurable F)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (hFiberVariation :
      ∀ g h : Matrix.specialUnitaryGroup (Fin N) ℂ,
        |F (Function.update A fiber g) - F (Function.update A fiber h)| ≤
          variation fiber) :
    (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
      |(∫ C, F C
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
            H N hN beta hbeta B target source fiber (k₁ source) g₂ A) -
        (∫ C, F C
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
            H N hN beta hbeta B target source fiber (k₂ source) g₂ A)|) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryInfluenceOperator
        H beta variation fiber := by
  rfl

end

end MathlibAnalytic
end MGAP4D
