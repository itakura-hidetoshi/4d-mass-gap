import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferCrossBoundarySourceProfileVariance
import Mathlib.Tactic

/-!
# Cross-boundary current target mean as a genuine source section

PR #4956 controls the variance of the source-value profile

  k ↦ CrossBoundaryTargetMean(B,A,k)

under the actual opposite-boundary source fiber.

This file records the exact geometric fact needed for the next outer
integration step: that profile is literally the source-coordinate section of
one current-value scalar observable on the two-boundary configuration space.

No new probability law, comparison coefficient, cutoff, or cardinality factor
is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory

noncomputable section

local instance crossBoundaryCurrentTargetSectionSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance crossBoundaryCurrentTargetSectionSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance crossBoundaryCurrentTargetSectionSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance crossBoundaryCurrentTargetSectionSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance crossBoundaryCurrentTargetSectionSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance crossBoundaryCurrentTargetSectionSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Evaluate the cross-boundary target mean at the actual current value of the
opposite-boundary source coordinate. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean
    H N hN beta hbeta source target F B A (B source)

/-- The source-value target-mean profile from #4956 is exactly the
source-coordinate section of the current target mean. This is a pointwise
identity and does not use source invariance. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean_eq_currentTargetMean_sourceSection
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (k : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean
        H N hN beta hbeta source target F B A k =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean
        H N hN beta hbeta source target F
        (Function.update B source k) A := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean
  simp

/-- For a source-invariant representative, the current target mean is the
literal frozen target-fiber expectation under the actual current
kernel-section target law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean_eq_frozen_of_sourceInvariant
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hInvariant :
      ∀ (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (value : Matrix.specialUnitaryGroup (Fin N) ℂ),
        F (Function.update left source value, right) = F (left, right))
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean
        H N hN beta hbeta source target F B A =
      ∫ g,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryFrozenTargetSection
          H N target F B A g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
          H N hN beta hbeta B A target := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean_eq_frozen_of_sourceInvariant
      H N hN beta hbeta source target F hInvariant B A (B source)]
  simp

/-- The source-profile variance from #4956 is exactly the conditional variance
of the current target mean along the opposite-boundary source coordinate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean_variance_eq_currentTargetMean_sourceSection_variance
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    variance
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean
          H N hN beta hbeta source target F B A)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
          H N hN beta hbeta A B source) =
      variance
        (fun k =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean
            H N hN beta hbeta source target F
            (Function.update B source k) A)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
          H N hN beta hbeta A B source) := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
      H N hN beta hbeta A B source
  have hSection :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean
          H N hN beta hbeta source target F B A =
        (fun k =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean
            H N hN beta hbeta source target F
            (Function.update B source k) A) := by
    funext k
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean_eq_currentTargetMean_sourceSection
        H N hN beta hbeta source target F B A k
  change variance _ μ = variance _ μ
  exact congrArg (fun M : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ => variance M μ) hSection

/-- #4956 rewritten in the section form needed for the outer stationarity
step. The coefficient is unchanged. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean_sourceSection_variance_le_crossCoefficient_sq_mul_integral_targetVarianceProfile
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hBetaLt :
      beta <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBetaThreshold)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (hInvariant :
      ∀ (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (value : Matrix.specialUnitaryGroup (Fin N) ℂ),
        F (Function.update left source value, right) = F (left, right))
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    variance
        (fun k =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean
            H N hN beta hbeta source target F
            (Function.update B source k) A)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
          H N hN beta hbeta A B source) ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
        beta) ^ 2 *
        ∫ k,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetVarianceProfile
            H N hN beta hbeta source target F B A k
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
            H N hN beta hbeta A B source := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
      H N hN beta hbeta A B source
  let M :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean
      H N hN beta hbeta source target F B A
  let Msection :=
    fun k =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean
        H N hN beta hbeta source target F
        (Function.update B source k) A
  have hEq :
      variance Msection μ = variance M μ := by
    symm
    simpa [μ, M, Msection] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean_variance_eq_currentTargetMean_sourceSection_variance
        H N hN beta hbeta source target F B A
  calc
    variance Msection μ = variance M μ := hEq
    _ ≤
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
          beta) ^ 2 *
          ∫ k,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetVarianceProfile
              H N hN beta hbeta source target F B A k
            ∂μ := by
      simpa [μ, M] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean_variance_le_crossCoefficient_sq_mul_integral_targetVarianceProfile
          H N hN beta hbeta hBetaLt source target F hF bound hbound hInvariant B A

end

end MathlibAnalytic
end MGAP4D
