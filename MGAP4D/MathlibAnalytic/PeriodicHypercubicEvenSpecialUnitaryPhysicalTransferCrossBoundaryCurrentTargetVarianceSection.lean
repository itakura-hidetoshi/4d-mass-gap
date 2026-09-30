import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferCrossBoundaryCurrentTargetSection
import Mathlib.Tactic

/-!
# Cross-boundary target variance as a genuine source section

PR #4957 identifies the cross-boundary target-mean profile with the
source-coordinate section of one current scalar observable.

The right-hand side of that variance estimate still uses the auxiliary target
variance profile indexed by the source value.  This file removes that last
presentation gap.  For source-invariant concrete representatives, the target
variance profile is exactly the source-coordinate section of the current
target conditional variance.

Thus both sides of the #4957 estimate are now expressed as source sections of
current two-boundary quantities.  This is the pointwise geometry required
before applying the existing one-link stationarity and joint/swap
disintegration machinery.

No coefficient, cutoff, probability law, factor two, link-count factor, or
volume factor is changed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory

noncomputable section

local instance crossBoundaryCurrentTargetVarianceSectionSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance crossBoundaryCurrentTargetVarianceSectionSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance crossBoundaryCurrentTargetVarianceSectionSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance crossBoundaryCurrentTargetVarianceSectionSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance crossBoundaryCurrentTargetVarianceSectionSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance crossBoundaryCurrentTargetVarianceSectionSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Target conditional variance under the actual current kernel-section law. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  variance
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryFrozenTargetSection
      H N target F B A)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
      H N hN beta hbeta B A target)

/-- At the actual current source value, the #4956 target variance profile is
definitionally the current target variance.  No source invariance is needed. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetVarianceProfile_currentValue_eq_currentTargetVariance
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetVarianceProfile
        H N hN beta hbeta source target F B A (B source) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance
        H N hN beta hbeta target F B A := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetVarianceProfile
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance
  simp

/-- For a source-invariant representative, the complete target variance
profile is exactly the source-coordinate section of the current target
variance.  The observable-section equality is proved first and then lifted
through variance by one nonrecursive congruence step. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetVarianceProfile_eq_currentTargetVariance_sourceSection_of_sourceInvariant
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
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetVarianceProfile
        H N hN beta hbeta source target F B A k =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance
        H N hN beta hbeta target F
        (Function.update B source k) A := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
      H N hN beta hbeta (Function.update B source k) A target
  let phi :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryFrozenTargetSection
      H N target F B A
  let psi :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryFrozenTargetSection
      H N target F (Function.update B source k) A
  have hSection : phi = psi := by
    funext g
    unfold
      phi psi
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryFrozenTargetSection
    exact (hInvariant B (Function.update A target g) k).symm
  change variance phi μ = variance psi μ
  exact
    congrArg
      (fun M : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ => variance M μ)
      hSection

/-- #4957 with the right-hand side rewritten entirely as the current target
variance along the source-coordinate section.  The cross coefficient is
literally unchanged. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean_sourceSection_variance_le_crossCoefficient_sq_mul_integral_currentTargetVariance_sourceSection
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
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance
            H N hN beta hbeta target F
            (Function.update B source k) A
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
            H N hN beta hbeta A B source := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
      H N hN beta hbeta A B source
  let c :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
      beta
  let V :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetVarianceProfile
      H N hN beta hbeta source target F B A
  let W :=
    fun k =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance
        H N hN beta hbeta target F
        (Function.update B source k) A
  have hBase :
      variance
          (fun k =>
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean
              H N hN beta hbeta source target F
              (Function.update B source k) A)
          μ ≤
        c ^ 2 * ∫ k, V k ∂μ := by
    simpa [μ, c, V] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean_sourceSection_variance_le_crossCoefficient_sq_mul_integral_targetVarianceProfile
        H N hN beta hbeta hBetaLt source target F hF bound hbound hInvariant B A
  have hIntegral :
      (∫ k, V k ∂μ) = ∫ k, W k ∂μ := by
    apply integral_congr_ae
    filter_upwards with k
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetVarianceProfile_eq_currentTargetVariance_sourceSection_of_sourceInvariant
        H N hN beta hbeta source target F hInvariant B A k
  change
    variance
        (fun k =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean
            H N hN beta hbeta source target F
            (Function.update B source k) A)
        μ ≤
      c ^ 2 * ∫ k, W k ∂μ
  calc
    variance
        (fun k =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean
            H N hN beta hbeta source target F
            (Function.update B source k) A)
        μ ≤
      c ^ 2 * ∫ k, V k ∂μ := hBase
    _ = c ^ 2 * ∫ k, W k ∂μ :=
      congrArg (fun x : ℝ => c ^ 2 * x) hIntegral

end

end MathlibAnalytic
end MGAP4D
