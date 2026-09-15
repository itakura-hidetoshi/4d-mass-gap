import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceDistinctFiberSecondBoundaryTransport
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance referenceDistinctFiberTwoStepTransportSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance referenceDistinctFiberTwoStepTransportSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance referenceDistinctFiberTwoStepTransportSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance referenceDistinctFiberTwoStepTransportSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance referenceDistinctFiberTwoStepTransportSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance referenceDistinctFiberTwoStepTransportSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Assumption-free physical two-step boundary transport for two distinct
continuous-C5 heat-bath fibers.  The previously abstract first- and
second-boundary obligations are discharged respectively by the literal-C5
off-fiber conditional-law transport and by averaging the one-link
cross-boundary estimate against the common first-step probability kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiber_twoStepHeatBath_transport_le
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
          H N hN beta hbeta B target source fiber₁ fiber₂ k₂ k₂ g₂ A F| ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta fiber₂ source * variation fiber₂ +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta fiber₁ source *
          (variation fiber₁ +
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
              beta * variation fiber₂) := by
  let offFiberInfluence :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ :=
    fun _target _source =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
        beta
  have hOffFiberInfluenceNonneg :
      ∀ target source, 0 ≤ offFiberInfluence target source := by
    intro target source
    dsimp [offFiberInfluence]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence_nonneg
        beta hbeta
  have hFirstBoundary :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiber_twoStepHeatBath_firstBoundary_le
      H N hN beta hbeta B target source fiber₁ fiber₂ hDistinct
      k₁ k₂ g₂ A F hF variation hVariationNonneg hVariation
  have hSecondBoundary :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiber_twoStepHeatBath_secondBoundary_le
      H N hN beta hbeta B target source fiber₁ fiber₂ hDistinct
      k₁ k₂ g₂ A F hF variation hVariationNonneg hVariation
  have hTransport :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiber_twoStepHeatBath_transportCriterion
      H N hN beta hbeta B target source fiber₁ fiber₂ hDistinct
      k₁ k₂ g₂ A F variation offFiberInfluence hOffFiberInfluenceNonneg
      (by
        simpa [offFiberInfluence] using hFirstBoundary)
      hSecondBoundary
  have hCarrierEq :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTagged_twoTargetUpdatedVariation_rightSource_eq
      H beta hbeta offFiberInfluence hOffFiberInfluenceNonneg variation
      fiber₁ fiber₂ source hDistinct
  rw [hCarrierEq] at hTransport
  simpa [offFiberInfluence] using hTransport

end

end MathlibAnalytic
end MGAP4D
