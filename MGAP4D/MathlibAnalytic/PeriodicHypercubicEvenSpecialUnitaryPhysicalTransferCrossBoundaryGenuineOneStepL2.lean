import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferCrossBoundaryCurrentTargetMeanSwapCarrier
import Mathlib.Tactic

/-!
# Genuine cross-boundary one-step L2 influence estimate

PR #4961 closes the target-variance side of the cross-boundary estimate against
the genuine right-target one-link residual. PR #4962 closes the source-variance
side against the genuine left-source leakage of the genuine right-target
projection.

This file performs only the remaining scalar/integration step.  The pointwise
real variance inequality from #4958 is converted to ENNReal using the already
proved integrability and nonnegativity of the target variance profile, then
integrated over the exact swapped vacuum/kernel-section carrier.

The result is the genuine cross-boundary one-step estimate

  || P_right,target f - P_left,source (P_right,target f) ||^2
    <= c_cross(beta)^2 || f - P_right,target f ||^2

for bounded strongly measurable concrete representatives invariant under the
left source coordinate.

No new coefficient, cutoff, factor two, link-count factor, or volume factor is
introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance crossBoundaryGenuineOneStepL2SpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance crossBoundaryGenuineOneStepL2SpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance crossBoundaryGenuineOneStepL2SecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance crossBoundaryGenuineOneStepL2MeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance crossBoundaryGenuineOneStepL2BorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance crossBoundaryGenuineOneStepL2SpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- ENNReal form of the fixed-background #4958 inequality.  The real target
variance integral is converted exactly to a lower integral using its existing
integrability and pointwise nonnegativity. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean_sourceSection_variance_ofReal_le_crossCoefficient_sq_mul_lintegral_currentTargetVariance_sourceSection
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
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    ENNReal.ofReal
        (variance
          (fun k =>
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean
              H N hN beta hbeta source target F
              (Function.update B source k) A)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
            H N hN beta hbeta A B source)) ≤
      ENNReal.ofReal
          ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
            beta) ^ 2) *
        ∫⁻ k,
          ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance
              H N hN beta hbeta target F
              (Function.update B source k) A)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
            H N hN beta hbeta A B source := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
      H N hN beta hbeta A B source
  let c :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
      beta
  let V :=
    fun k =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance
        H N hN beta hbeta target F
        (Function.update B source k) A
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetVarianceProfile
      H N hN beta hbeta source target F B A
  have hPV : P = V := by
    funext k
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetVarianceProfile_eq_currentTargetVariance_sourceSection_of_sourceInvariant
        H N hN beta hbeta source target F hInvariant B A k
  have hV :
      Integrable V μ := by
    rw [← hPV]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryTargetVarianceProfile_integrable_swappedSourceFiber
        H N hN beta hbeta source target F hF bound hbound B A
  have hVNonneg : ∀ k, 0 ≤ V k := by
    intro k
    exact variance_nonneg _ _
  have hReal :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean_sourceSection_variance_le_crossCoefficient_sq_mul_integral_currentTargetVariance_sourceSection
      H N hN beta hbeta hBetaLt source target F hF bound hbound hInvariant B A
  have hEN :
      ENNReal.ofReal
          (variance
            (fun k =>
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean
                H N hN beta hbeta source target F
                (Function.update B source k) A)
            μ) ≤
        ENNReal.ofReal (c ^ 2 * ∫ k, V k ∂μ) :=
    ENNReal.ofReal_le_ofReal hReal
  rw [
    ENNReal.ofReal_mul (sq_nonneg c),
    ofReal_integral_eq_lintegral_ofReal hV
      (ae_of_all μ hVNonneg)] at hEN
  simpa [μ, c, V] using hEN

/-- Outer integration of the fixed-background ENNReal estimate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean_sourceSection_variance_vacuum_lintegral_le_crossCoefficient_sq_mul_sourceUpdateTargetVariance
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
        F (Function.update left source value, right) = F (left, right)) :
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
        H N hN beta hbeta) ≤
      ENNReal.ofReal
          ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
            beta) ^ 2) *
        (∫⁻ A,
          (∫⁻ B,
            (∫⁻ k,
              ENNReal.ofReal
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance
                  H N hN beta hbeta target F
                  (Function.update B source k) A)
              ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
                H N hN beta hbeta A B source)
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
              H N hN beta hbeta A)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
            H N hN beta hbeta) := by
  let cEN : ℝ≥0∞ :=
    ENNReal.ofReal
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
        beta) ^ 2)
  have hInner :
      ∀ A,
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
            H N hN beta hbeta A) ≤
          cEN *
            ∫⁻ B,
              (∫⁻ k,
                ENNReal.ofReal
                  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance
                    H N hN beta hbeta target F
                    (Function.update B source k) A)
                ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
                  H N hN beta hbeta A B source)
              ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
                H N hN beta hbeta A := by
    intro A
    calc
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
          H N hN beta hbeta A) ≤
        ∫⁻ B,
          cEN *
            (∫⁻ k,
              ENNReal.ofReal
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance
                  H N hN beta hbeta target F
                  (Function.update B source k) A)
              ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
                H N hN beta hbeta A B source)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta A := by
        apply lintegral_mono
        intro B
        simpa [cEN] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean_sourceSection_variance_ofReal_le_crossCoefficient_sq_mul_lintegral_currentTargetVariance_sourceSection
            H N hN beta hbeta hBetaLt source target F hF bound hbound hInvariant A B
      _ =
        cEN *
          ∫⁻ B,
            (∫⁻ k,
              ENNReal.ofReal
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance
                  H N hN beta hbeta target F
                  (Function.update B source k) A)
              ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
                H N hN beta hbeta A B source)
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
              H N hN beta hbeta A := by
        exact lintegral_const_mul' cEN _ ENNReal.ofReal_ne_top
  calc
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
        H N hN beta hbeta) ≤
      ∫⁻ A,
        cEN *
          (∫⁻ B,
            (∫⁻ k,
              ENNReal.ofReal
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance
                  H N hN beta hbeta target F
                  (Function.update B source k) A)
              ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
                H N hN beta hbeta A B source)
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
              H N hN beta hbeta A)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta := by
      apply lintegral_mono
      intro A
      exact hInner A
    _ =
      cEN *
        (∫⁻ A,
          (∫⁻ B,
            (∫⁻ k,
              ENNReal.ofReal
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance
                  H N hN beta hbeta target F
                  (Function.update B source k) A)
              ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
                H N hN beta hbeta A B source)
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
              H N hN beta hbeta A)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
            H N hN beta hbeta) := by
      exact lintegral_const_mul' cEN _ ENNReal.ofReal_ne_top
    _ =
      ENNReal.ofReal
          ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
            beta) ^ 2) *
        (∫⁻ A,
          (∫⁻ B,
            (∫⁻ k,
              ENNReal.ofReal
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance
                  H N hN beta hbeta target F
                  (Function.update B source k) A)
              ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
                H N hN beta hbeta A B source)
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
              H N hN beta hbeta A)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
            H N hN beta hbeta) := by
      rfl

/-- ENNReal genuine cross-boundary one-step leakage estimate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundary_leftLeakage_norm_sq_ofReal_le_crossCoefficient_sq_mul_targetResidual
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
        F (Function.update left source value, right) = F (left, right)) :
    ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
              H N hN beta hbeta target
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                H N hN beta hbeta F hF bound hbound) -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
              H N hN beta hbeta source
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
                H N hN beta hbeta target
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                  H N hN beta hbeta F hF bound hbound))‖ ^ 2) ≤
      ENNReal.ofReal
          ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
            beta) ^ 2) *
        ENNReal.ofReal
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                H N hN beta hbeta F hF bound hbound -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
                H N hN beta hbeta target
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                  H N hN beta hbeta F hF bound hbound)‖ ^ 2) := by
  have hIntegrated :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean_sourceSection_variance_vacuum_lintegral_le_crossCoefficient_sq_mul_sourceUpdateTargetVariance
      H N hN beta hbeta hBetaLt source target F hF bound hbound hInvariant
  have hRHS :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetVariance_sourceUpdate_vacuum_lintegral_le_condExpL2_residual_norm_sq
      H N hN beta hbeta source target F hF bound hbound
  have hFinal :=
    hIntegrated.trans
      (mul_le_mul_left'
        hRHS
        (ENNReal.ofReal
          ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
            beta) ^ 2)))
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundaryCurrentTargetMean_sourceSection_variance_vacuum_lintegral_eq_leftLeakageNormSq
      H N hN beta hbeta source target F hF bound hbound] at hFinal
  exact hFinal

/-- Real squared-norm form of the genuine cross-boundary one-step estimate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundary_leftLeakage_norm_sq_le_crossCoefficient_sq_mul_targetResidual
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
              H N hN beta hbeta F hF bound hbound))‖ ^ 2 ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
        beta) ^ 2 *
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
              H N hN beta hbeta F hF bound hbound -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
              H N hN beta hbeta target
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                H N hN beta hbeta F hF bound hbound)‖ ^ 2 := by
  have hEN :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCrossBoundary_leftLeakage_norm_sq_ofReal_le_crossCoefficient_sq_mul_targetResidual
      H N hN beta hbeta hBetaLt source target F hF bound hbound hInvariant
  have hCoeff :
      0 ≤
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
          beta) ^ 2 :=
    sq_nonneg _
  have hRHSNonneg :
      0 ≤
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
          beta) ^ 2 *
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                H N hN beta hbeta F hF bound hbound -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
                H N hN beta hbeta target
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                  H N hN beta hbeta F hF bound hbound)‖ ^ 2 :=
    mul_nonneg hCoeff (sq_nonneg _)
  have hEN' :
      ENNReal.ofReal
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
                H N hN beta hbeta target
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                  H N hN beta hbeta F hF bound hbound) -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
                H N hN beta hbeta source
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
                  H N hN beta hbeta target
                  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                    H N hN beta hbeta F hF bound hbound))‖ ^ 2) ≤
        ENNReal.ofReal
          ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
            beta) ^ 2 *
            ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                  H N hN beta hbeta F hF bound hbound -
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
                  H N hN beta hbeta target
                  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                    H N hN beta hbeta F hF bound hbound)‖ ^ 2) := by
    simpa [ENNReal.ofReal_mul hCoeff] using hEN
  exact
    (ENNReal.ofReal_le_ofReal_iff hRHSNonneg).mp hEN'

end

end MathlibAnalytic
end MGAP4D
