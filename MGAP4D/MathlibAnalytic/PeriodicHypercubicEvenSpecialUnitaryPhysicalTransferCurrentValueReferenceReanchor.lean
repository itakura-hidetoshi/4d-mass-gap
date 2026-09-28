import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferDiagonalReferenceFullKernelSectionLaw
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceOneLinkHeatBathReversibility
import Mathlib.Tactic

/-!
# Exact re-anchoring of current-value reference laws

At current-value parameters every continuous-vacuum reference law is already
the same fixed-right kernel-section law.  Consequently the bookkeeping choice
of reference target/source may be changed exactly, provided each parameter is
reset to the current value of the same outer boundary.

This file exposes that fact at the three levels needed by the backward-direct
mean closure:

* the complete normalized reference probability law;
* every literal one-link fiber / conditional law;
* every one-link heat-bath projection and transition kernel.

These are equality theorems.  They introduce no comparison coefficient,
response symmetry, Harnack estimate, or source/target exchange assumption.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory

noncomputable section

local instance currentValueReferenceReanchorSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance currentValueReferenceReanchorSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance currentValueReferenceReanchorSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance currentValueReferenceReanchorSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance currentValueReferenceReanchorSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance currentValueReferenceReanchorSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Any two current-value presentations of the complete reference law are
literally the same probability measure. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_currentValue_reanchor
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (referenceTarget₁ referenceSource₁ referenceTarget₂ referenceSource₂ :
      PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta C referenceTarget₁ referenceSource₁
        (C referenceSource₁) (C referenceTarget₁) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta C referenceTarget₂ referenceSource₂
        (C referenceSource₂) (C referenceTarget₂) := by
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta C referenceTarget₁ referenceSource₁
        (C referenceSource₁) (C referenceTarget₁) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta C :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_diagonalCurrentValues_eq_kernelSection
        H N hN beta hbeta C referenceTarget₁ referenceSource₁
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta C referenceTarget₂ referenceSource₂
        (C referenceSource₂) (C referenceTarget₂) :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_diagonalCurrentValues_eq_kernelSection
        H N hN beta hbeta C referenceTarget₂ referenceSource₂).symm

/-- Any two current-value presentations of the same resampled fiber law are
literally the same one-link probability measure, at every background A. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_currentValue_reanchor
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (referenceTarget₁ referenceSource₁ referenceTarget₂ referenceSource₂ fiber :
      PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta C referenceTarget₁ referenceSource₁ fiber
        (C referenceSource₁) (C referenceTarget₁) A =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta C referenceTarget₂ referenceSource₂ fiber
        (C referenceSource₂) (C referenceTarget₂) A := by
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta C referenceTarget₁ referenceSource₁ fiber
        (C referenceSource₁) (C referenceTarget₁) A =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
        H N hN beta hbeta C A fiber :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_diagonalCurrentValues_eq_kernelSectionSpatialLinkNormalizedMeasure
        H N hN beta hbeta C A referenceTarget₁ referenceSource₁ fiber
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta C referenceTarget₂ referenceSource₂ fiber
        (C referenceSource₂) (C referenceTarget₂) A :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_diagonalCurrentValues_eq_kernelSectionSpatialLinkNormalizedMeasure
        H N hN beta hbeta C A referenceTarget₂ referenceSource₂ fiber).symm

/-- Current-value conditional kernels agree pointwise after re-anchoring the
reference target/source bookkeeping. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel_currentValue_reanchor_apply
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (referenceTarget₁ referenceSource₁ referenceTarget₂ referenceSource₂ fiber :
      PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel
        H N hN beta hbeta C referenceTarget₁ referenceSource₁ fiber
        (C referenceSource₁) (C referenceTarget₁) A =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel
        H N hN beta hbeta C referenceTarget₂ referenceSource₂ fiber
        (C referenceSource₂) (C referenceTarget₂) A := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel_apply,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel_apply]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_currentValue_reanchor
      H N hN beta hbeta C A
      referenceTarget₁ referenceSource₁ referenceTarget₂ referenceSource₂ fiber

/-- Current-value heat-bath projections agree exactly after re-anchoring the
reference target/source bookkeeping. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection_currentValue_reanchor
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (referenceTarget₁ referenceSource₁ referenceTarget₂ referenceSource₂ fiber :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hX : StronglyMeasurable X) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection
        H N hN beta hbeta C referenceTarget₁ referenceSource₁ fiber
        (C referenceSource₁) (C referenceTarget₁) X A =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection
        H N hN beta hbeta C referenceTarget₂ referenceSource₂ fiber
        (C referenceSource₂) (C referenceTarget₂) X A := by
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection
        H N hN beta hbeta C referenceTarget₁ referenceSource₁ fiber
        (C referenceSource₁) (C referenceTarget₁) X A =
      ∫ g,
        X (Function.update A fiber g)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
          H N hN beta hbeta C A fiber :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection_diagonalCurrentValues_eq_kernelSectionSpatialLinkIntegral
        H N hN beta hbeta C A referenceTarget₁ referenceSource₁ fiber X hX
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection
        H N hN beta hbeta C referenceTarget₂ referenceSource₂ fiber
        (C referenceSource₂) (C referenceTarget₂) X A :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection_diagonalCurrentValues_eq_kernelSectionSpatialLinkIntegral
        H N hN beta hbeta C A referenceTarget₂ referenceSource₂ fiber X hX).symm

/-- Current-value one-link heat-bath transition kernels agree pointwise after
re-anchoring the reference target/source bookkeeping. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_currentValue_reanchor_apply
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (referenceTarget₁ referenceSource₁ referenceTarget₂ referenceSource₂ fiber :
      PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
        H N hN beta hbeta C referenceTarget₁ referenceSource₁ fiber
        (C referenceSource₁) (C referenceTarget₁) A =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
        H N hN beta hbeta C referenceTarget₂ referenceSource₂ fiber
        (C referenceSource₂) (C referenceTarget₂) A := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_apply_eq_map,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_apply_eq_map]
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_currentValue_reanchor
      H N hN beta hbeta C A
      referenceTarget₁ referenceSource₁ referenceTarget₂ referenceSource₂ fiber]

end

end MGAP4D.MathlibAnalytic
