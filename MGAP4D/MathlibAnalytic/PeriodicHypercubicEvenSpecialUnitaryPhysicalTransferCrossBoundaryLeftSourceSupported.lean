import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferCrossBoundaryLeftSourceUpdate
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCrossBoundaryRowSum
import Mathlib.Tactic

/-!
# Preserve exact diagonal support in the genuine cross-boundary leakage

PR #4964 applies the genuine cross-boundary estimate to an actual left one-link
update, but states the uniform diagonal coefficient `c_cross(beta)`.

The underlying C5 one-link law has a stronger exact support statement:
changing the opposite-boundary source can influence a target fiber only when
the two spatial links coincide.  This file transports that exact support
through the already-established source-profile variance and genuine joint L2
bridges.

For distinct source and target links the cross-boundary target-mean profile is
pointwise constant in the source value, so its source variance is exactly zero.
The #4962 identity then forces the genuine left-source leakage norm to vanish.

Combining this zero statement with #4964 on the diagonal yields the actual
left-source update bound with the existing one-point-supported majorant

  crossMajorant(beta,target,source).

This is exactly the off-diagonal block used by the two-boundary Schur matrix.
No link-count or volume factor is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

noncomputable section

local instance crossBoundaryLeftSourceSupportedSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance crossBoundaryLeftSourceSupportedSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance crossBoundaryLeftSourceSupportedSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance crossBoundaryLeftSourceSupportedSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance crossBoundaryLeftSourceSupportedSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance crossBoundaryLeftSourceSupportedSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Off the diagonal `source = target`, the actual cross-boundary target mean
is independent of the source value.  We expose the exact squared-zero form
already present inside the C5 support theorem. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean_pairwise_sq_eq_zero_of_ne
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hBetaLt :
      beta <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBetaThreshold)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : source ≠ target)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (hInvariant :
      ∀ (left right :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (value : Matrix.specialUnitaryGroup (Fin N) ℂ),
        F (Function.update left source value, right) = F (left, right))
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (k₁ k₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean
        H N hN beta hbeta source target F B A k₁ -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean
        H N hN beta hbeta source target F B A k₂) ^ 2 = 0 := by
  let phi :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryFrozenTargetSection
      H N target F B A
  have hphi₁ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryFrozenTargetSection_memLp_two
      H N hN beta hbeta source target F hF bound hbound B A k₁
  have hphi₂ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryFrozenTargetSection_memLp_two
      H N hN beta hbeta source target F hF bound hbound B A k₂
  have hSupported :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure_crossBoundary_L2MeanDifference_sq_le_varianceSum_supported_on_diagonal
      H N hN beta hbeta hBetaLt B target source target k₁ k₂ A
      phi hphi₁ hphi₂
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean_eq_frozen_of_sourceInvariant
      H N hN beta hbeta source target F hInvariant B A k₁,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean_eq_frozen_of_sourceInvariant
      H N hN beta hbeta source target F hInvariant B A k₂]
  have hle :
      ((∫ g, phi g
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
            H N hN beta hbeta (Function.update B source k₁) A target) -
        (∫ g, phi g
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
            H N hN beta hbeta (Function.update B source k₂) A target)) ^ 2 ≤ 0 := by
    simpa [hne] using hSupported
  exact le_antisymm hle (sq_nonneg _)

/-- The source-coordinate variance of the current target mean is therefore
pointwise zero for distinct cross-boundary links. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean_sourceSection_variance_eq_zero_of_ne
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hBetaLt :
      beta <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBetaThreshold)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : source ≠ target)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (hInvariant :
      ∀ (left right :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (value : Matrix.specialUnitaryGroup (Fin N) ℂ),
        F (Function.update left source value, right) = F (left, right))
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    variance
        (fun k =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean
            H N hN beta hbeta source target F
            (Function.update B source k) A)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
          H N hN beta hbeta A B source) = 0 := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
      H N hN beta hbeta A B source
  let M :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean
      H N hN beta hbeta source target F B A
  letI : IsProbabilityMeasure μ := by
    change IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
        H N hN beta hbeta A B source)
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundarySwappedSourceFiber_isProbabilityMeasure
        H N hN beta hbeta source B A
  have hPoint : ∀ k, M k = M (B source) := by
    intro k
    have hz :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean_pairwise_sq_eq_zero_of_ne
        H N hN beta hbeta hBetaLt source target hne F hF bound hbound
        hInvariant B A k (B source)
    change (M k - M (B source)) ^ 2 = 0 at hz
    nlinarith [sq_nonneg (M k - M (B source))]
  have hConst : M = fun _ => M (B source) := by
    funext k
    exact hPoint k
  have hVarM : variance M μ = 0 := by
    rw [hConst]
    have hZero :=
      variance_const_add
        (μ := μ)
        (X := fun _ : Matrix.specialUnitaryGroup (Fin N) ℂ => 0)
        stronglyMeasurable_const.aestronglyMeasurable
        (M (B source))
    simpa using hZero
  calc
    variance
        (fun k =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean
            H N hN beta hbeta source target F
            (Function.update B source k) A)
        μ =
      variance M μ := by
        symm
        simpa [μ, M] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetMean_variance_eq_currentTargetMean_sourceSection_variance
            H N hN beta hbeta source target F B A
    _ = 0 := hVarM

/-- For a bounded left-source-invariant concrete representative, distinct
cross-boundary links have exactly zero genuine L2 leakage. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundary_leftLeakage_norm_eq_zero_of_ne
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hBetaLt :
      beta <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBetaThreshold)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : source ≠ target)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (hInvariant :
      ∀ (left right :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (value : Matrix.specialUnitaryGroup (Fin N) ℂ),
        F (Function.update left source value, right) = F (left, right)) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN beta hbeta target
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
            H N hN beta hbeta F hF bound hbound) -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
          H N hN beta hbeta source
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN beta hbeta target
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
              H N hN beta hbeta F hF bound hbound))‖ = 0 := by
  let leak :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN beta hbeta target
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
            H N hN beta hbeta F hF bound hbound) -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
          H N hN beta hbeta source
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN beta hbeta target
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
              H N hN beta hbeta F hF bound hbound))‖
  have hBridge :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean_sourceSection_variance_vacuum_lintegral_eq_leftLeakageNormSq
      H N hN beta hbeta source target F hF bound hbound
  have hIntegralZero :
      (∫⁻ A,
        (∫⁻ B,
          ENNReal.ofReal
            (variance
              (fun k =>
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean
                  H N hN beta hbeta source target F
                  (Function.update B source k) A)
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
                H N hN beta hbeta A B source))
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta A)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta) = 0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards with A
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards with B
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean_sourceSection_variance_eq_zero_of_ne
        H N hN beta hbeta hBetaLt source target hne
        F hF bound hbound hInvariant B A]
    simp
  have hOfReal : ENNReal.ofReal (leak ^ 2) = 0 := by
    change _ = ENNReal.ofReal (leak ^ 2) at hBridge
    rw [hIntegralZero] at hBridge
    exact hBridge.symm
  have hNonpos : leak ^ 2 ≤ 0 :=
    ENNReal.ofReal_eq_zero.mp hOfReal
  have hLeakNonneg : 0 ≤ leak := norm_nonneg _
  nlinarith

/-- The actual left-source update has exactly zero cross leakage when the
opposite-boundary target is a distinct spatial link. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundary_leftSourceUpdate_leakage_norm_eq_zero_of_ne
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hBetaLt :
      beta <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBetaThreshold)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : source ≠ target)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hf :
      f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN beta hbeta target
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
            H N hN beta hbeta source f) -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
          H N hN beta hbeta source
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN beta hbeta target
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
              H N hN beta hbeta source f))‖ = 0 := by
  obtain ⟨G, hG, bound, hbound, hRep, hInvariant⟩ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2_exists_bounded_leftSourceInvariant_representative
      H N hN beta hbeta source f hf
  have hZero :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundary_leftLeakage_norm_eq_zero_of_ne
      H N hN beta hbeta hBetaLt source target hne
      G hG bound hbound hInvariant
  rw [hRep] at hZero
  exact hZero

/-- Exact support-preserving actual left-source cross-boundary leakage bound.
The coefficient is literally the one-point-supported cross majorant used by the
two-boundary Schur kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundary_leftSourceUpdate_leakage_norm_le_crossMajorant
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hBetaLt :
      beta <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBetaThreshold)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hf :
      f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN beta hbeta target
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
            H N hN beta hbeta source f) -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
          H N hN beta hbeta source
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN beta hbeta target
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
              H N hN beta hbeta source f))‖ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta target source *
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
              H N hN beta hbeta source f -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
              H N hN beta hbeta target
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
                H N hN beta hbeta source f)‖ := by
  by_cases hst : source = target
  · subst target
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundary_leftSourceUpdate_leakage_norm_le_crossCoefficient
        H N hN beta hbeta hBetaLt source source f hf
  · have hZero :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundary_leftSourceUpdate_leakage_norm_eq_zero_of_ne
        H N hN beta hbeta hBetaLt source target hst f hf
    rw [hZero]
    simp [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant,
      hst]

end

end MathlibAnalytic
end MGAP4D
