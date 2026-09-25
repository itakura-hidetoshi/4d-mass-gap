import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferDiagonalReferenceFiberKernelSectionLaw
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumRemoteKernelSectionOneLinkProjection
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceOneLinkHeatBathReversibility
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Tactic

/-!
# Diagonal remote projection as a kernel-section one-link integral

PR #4759 identifies, pointwise, the diagonal literal reference one-link fiber
law with the normalized fixed-right kernel-section one-link law.

This file transports the already-defined remote heat-bath projection through
that exact law identity.  At the diagonal current values, the projection is
literally the one-link kernel-section expectation of the updated observable.

The corresponding fluctuation therefore has the concrete form

  X(A) - ∫ X(A[target <- g]) d kappa_{C,A,target}(g).

No remote-separation hypothesis, comparison coefficient, or Poincare input is
used here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory

noncomputable section

attribute [local instance]
  continuousVacuumReferenceOneLinkFiberSpecialUnitaryIsTopologicalGroup
  continuousVacuumReferenceOneLinkFiberSpecialUnitaryCompactSpace
  continuousVacuumReferenceOneLinkFiberSpecialUnitarySecondCountableTopology
  continuousVacuumReferenceOneLinkFiberSpecialUnitaryMeasurableSpace
  continuousVacuumReferenceOneLinkFiberSpecialUnitaryBorelSpace
  continuousVacuumReferenceOneLinkFiberSpatialLinkFintype

/-- At diagonal current values, the remote one-link heat-bath projection is
exactly integration of the coordinate-updated observable against the literal
fixed-right kernel-section one-link law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_diagonal_eq_kernelSectionSpatialLinkIntegral
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hX : StronglyMeasurable X) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
        H N hN beta hbeta C target source target
        (C source) (C target) X A =
      ∫ g,
        X (Function.update A target g)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
          H N hN beta hbeta C A target := by
  have hUpdate :
      Measurable
        (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
          Function.update A target g) :=
    measurable_update A
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel_apply,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_apply_eq_map,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_diagonal_eq_kernelSectionSpatialLinkNormalizedMeasure
      H N hN beta hbeta C A target source]
  exact
    MeasureTheory.integral_map hUpdate.aemeasurable hX.aestronglyMeasurable

/-- The diagonal remote fluctuation is the observable value minus its literal
kernel-section one-link expectation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation_diagonal_eq_value_sub_kernelSectionSpatialLinkIntegral
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hX : StronglyMeasurable X) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
        H N hN beta hbeta C target source target
        (C source) (C target) X A =
      X A -
        ∫ g,
          X (Function.update A target g)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
            H N hN beta hbeta C A target := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_diagonal_eq_kernelSectionSpatialLinkIntegral
      H N hN beta hbeta C A target source X hX]

end

end MathlibAnalytic
end MGAP4D
