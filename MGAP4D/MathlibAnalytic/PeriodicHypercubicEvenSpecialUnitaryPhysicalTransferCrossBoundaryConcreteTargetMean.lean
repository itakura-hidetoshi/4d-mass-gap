import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferCrossBoundaryKernelSectionL2MeanDifference
import Mathlib.Tactic

/-!
# Concrete cross-boundary target means

The actual cross-boundary estimate is now available on source-updated
kernel-section one-link laws. This file inserts a bounded concrete joint
observable.

For a source-invariant observable, updating the opposite boundary source
changes only the target conditional law, not the observable section itself.
Hence #4954 applies with one common target-fiber test function and the exact
cross coefficient is preserved.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open ProbabilityTheory

noncomputable section

local instance crossBoundaryConcreteTargetMeanSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance crossBoundaryConcreteTargetMeanSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance crossBoundaryConcreteTargetMeanSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance crossBoundaryConcreteTargetMeanSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance crossBoundaryConcreteTargetMeanSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance crossBoundaryConcreteTargetMeanSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Actual opposite-boundary target mean after changing one source coordinate
of the fixed boundary. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (k : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  ∫ g,
    F (Function.update B source k, Function.update A target g)
    ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
      H N hN beta hbeta (Function.update B source k) A target

/-- The target-fiber observable obtained by freezing the original opposite
boundary. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryFrozenTargetSection
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  F (B, Function.update A target g)

/-- Source invariance removes the direct dependence of the target observable
section on the changed opposite-boundary source value. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean_eq_frozen_of_sourceInvariant
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
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (k : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean
        H N hN beta hbeta source target F B A k =
      ∫ g,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryFrozenTargetSection
          H N target F B A g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
          H N hN beta hbeta (Function.update B source k) A target := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryFrozenTargetSection
  apply integral_congr_ae
  filter_upwards with g
  rw [hInvariant B (Function.update A target g) k]

/-- The frozen target section is strongly measurable. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryFrozenTargetSection_stronglyMeasurable
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    StronglyMeasurable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryFrozenTargetSection
        H N target F B A) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryFrozenTargetSection
  exact hF.comp_measurable
    (measurable_const.prodMk (measurable_update A))

/-- A bounded concrete observable gives an L2 frozen target section under every
source-updated kernel-section target fiber. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryFrozenTargetSection_memLp_two
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (k : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    MemLp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryFrozenTargetSection
        H N target F B A)
      2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
        H N hN beta hbeta (Function.update B source k) A target) := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
      H N hN beta hbeta (Function.update B source k) A target
  let hLaw :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_currentTarget_eq_kernelSection_sourceUpdate
      H N hN beta hbeta B target source target k A
  letI : IsProbabilityMeasure μ := by
    change IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
        H N hN beta hbeta (Function.update B source k) A target)
    rw [← hLaw]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta B target source target k (B target) A
  apply MemLp.of_bound
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryFrozenTargetSection_stronglyMeasurable
      H N target F hF B A).aestronglyMeasurable
    |bound|
  filter_upwards with g
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryFrozenTargetSection
  exact (hbound (B, Function.update A target g)).trans (le_abs_self bound)

/-- Concrete source-invariant cross-boundary target means satisfy the exact
variance-sensitive pairwise estimate with the existing cross coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean_pairwise_sq_le_varianceSum
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
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (k₁ k₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean
        H N hN beta hbeta source target F B A k₁ -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean
        H N hN beta hbeta source target F B A k₂) ^ 2 ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
        beta) ^ 2 *
        (variance
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryFrozenTargetSection
              H N target F B A)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
              H N hN beta hbeta (Function.update B source k₁) A target) +
          variance
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryFrozenTargetSection
              H N target F B A)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
              H N hN beta hbeta (Function.update B source k₂) A target)) := by
  let phi :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryFrozenTargetSection
      H N target F B A
  have hphi₁ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryFrozenTargetSection_memLp_two
      H N hN beta hbeta source target F hF bound hbound B A k₁
  have hphi₂ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryFrozenTargetSection_memLp_two
      H N hN beta hbeta source target F hF bound hbound B A k₂
  have h :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure_crossBoundary_L2MeanDifference_sq_le_varianceSum_diagonal
      H N hN beta hbeta hBetaLt B target source k₁ k₂ A phi hphi₁ hphi₂
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean_eq_frozen_of_sourceInvariant
      H N hN beta hbeta source target F hInvariant B A k₁,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean_eq_frozen_of_sourceInvariant
      H N hN beta hbeta source target F hInvariant B A k₂]
  simpa [phi] using h

end

end MathlibAnalytic
end MGAP4D
