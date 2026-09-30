import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferCrossBoundaryReferenceFiberKernelSectionBridge
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCrossBoundaryL2MeanDifference
import Mathlib.Tactic

/-!
# Actual kernel-section cross-boundary L2 mean-difference estimate

PR #4949 proves the variance-sensitive cross-boundary estimate on the literal
continuous-vacuum reference one-link laws. PR #4953 identifies those laws,
at the actual current distinguished-target value, with the genuine fixed-right
kernel-section one-link laws after the right source is updated.

This file performs only that exact change of presentation. Therefore:

* the source/fiber support remains exactly diagonal;
* the coefficient remains exactly c_cross(beta);
* no new Harnack, triangle, cardinality, or volume factor appears.

The result is the model-specific conditional-law estimate needed before the
independent-pair cancellation and stationary residual steps.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open ProbabilityTheory

noncomputable section

local instance crossBoundaryKernelSectionL2SpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance crossBoundaryKernelSectionL2SpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance crossBoundaryKernelSectionL2SpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance crossBoundaryKernelSectionL2SpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance crossBoundaryKernelSectionL2SpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance crossBoundaryKernelSectionL2SpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Full exact support form on actual fixed-right kernel-section one-link laws.
Changing the right source value can influence a resampled left fiber only when
the source and fiber are the same spatial link. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure_crossBoundary_L2MeanDifference_sq_le_varianceSum_supported_on_diagonal
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hBetaLt :
      beta <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBetaThreshold)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k₁ k₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (phi : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hphi₁ : MemLp phi 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
        H N hN beta hbeta (Function.update B source k₁) A fiber))
    (hphi₂ : MemLp phi 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
        H N hN beta hbeta (Function.update B source k₂) A fiber)) :
    ((∫ g, phi g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
          H N hN beta hbeta (Function.update B source k₁) A fiber) -
      (∫ g, phi g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
          H N hN beta hbeta (Function.update B source k₂) A fiber)) ^ 2 ≤
      if source = fiber then
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
          beta) ^ 2 *
          (variance phi
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
                H N hN beta hbeta (Function.update B source k₁) A fiber) +
            variance phi
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
                H N hN beta hbeta (Function.update B source k₂) A fiber))
      else 0 := by
  have hLaw₁ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_currentTarget_eq_kernelSection_sourceUpdate
      H N hN beta hbeta B target source fiber k₁ A
  have hLaw₂ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_currentTarget_eq_kernelSection_sourceUpdate
      H N hN beta hbeta B target source fiber k₂ A
  have hphiRef₁ : MemLp phi 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta B target source fiber k₁ (B target) A) := by
    rw [hLaw₁]
    exact hphi₁
  have hphiRef₂ : MemLp phi 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta B target source fiber k₂ (B target) A) := by
    rw [hLaw₂]
    exact hphi₂
  have h :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_L2MeanDifference_sq_le_varianceSum_supported_on_diagonal
      H N hN beta hbeta hBetaLt B target source fiber
      k₁ k₂ (B target) A phi hphiRef₁ hphiRef₂
  simpa only [hLaw₁, hLaw₂] using h

/-- Diagonal specialization: the actual kernel-section source-update response
has exactly the previously named cross-boundary coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure_crossBoundary_L2MeanDifference_sq_le_varianceSum_diagonal
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hBetaLt :
      beta <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBetaThreshold)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k₁ k₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (phi : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hphi₁ : MemLp phi 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
        H N hN beta hbeta (Function.update B source k₁) A source))
    (hphi₂ : MemLp phi 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
        H N hN beta hbeta (Function.update B source k₂) A source)) :
    ((∫ g, phi g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
          H N hN beta hbeta (Function.update B source k₁) A source) -
      (∫ g, phi g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
          H N hN beta hbeta (Function.update B source k₂) A source)) ^ 2 ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
        beta) ^ 2 *
        (variance phi
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
              H N hN beta hbeta (Function.update B source k₁) A source) +
          variance phi
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
              H N hN beta hbeta (Function.update B source k₂) A source)) := by
  simpa using
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure_crossBoundary_L2MeanDifference_sq_le_varianceSum_supported_on_diagonal
      H N hN beta hbeta hBetaLt B target source source k₁ k₂ A phi hphi₁ hphi₂

end

end MathlibAnalytic
end MGAP4D
