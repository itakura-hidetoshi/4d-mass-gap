import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairCurrentValueFixedBackgroundFiberL2
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairSecondMeanRMSL2
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferDiagonalReferenceFullKernelSectionLaw
import MGAP4D.MathlibAnalytic.RealL2ExternalTensor
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Tactic

/-!
# Fixed-background RMS Fubini bridge

PRs #4820--#4822 slice the source-pair RMS carrier at one fixed outer
background while preserving the actual background-dependent physical envelope.
PR #4813, by contrast, controls the corresponding full source-pair L2 norm
after the outer background has already been integrated.

This file proves the exact bridge between those two presentations.

First, on an arbitrary fixed background, the squared norm of the
second-law-mean RMS L2 vector is exactly the lower integral of the pointwise
RMS square over the source-pair fiber.

Second, on the full source-pair carrier, the squared L2 norm is exactly the
lower integral of the same pointwise RMS square.

Finally, at current values

  B = C,
  k = C(distinguishedSource),
  g2 = C(source),

the outer reference law is exactly the fixed-right kernel-section probability
law and the full source-pair measure is its composition product with the
fixed-background source-pair fiber.  Therefore

  integral_A ofReal(||RMS_fiber(A)||^2)
    = ofReal(||RMS_full||^2).

No inequality, factor two, source summation, finite-cardinality factor,
pin-free replacement, or new probability law is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance fixedBackgroundRMSFubiniSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance fixedBackgroundRMSFubiniSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance fixedBackgroundRMSFubiniSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance fixedBackgroundRMSFubiniSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance fixedBackgroundRMSFubiniSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance fixedBackgroundRMSFubiniSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The fixed-background second-mean RMS squared L2 norm is exactly its
pointwise square lower integral on the source-pair fiber. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeFixedBackgroundL2_norm_sq_ofReal_eq_lintegral
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeFixedBackgroundL2
            H N hN beta hbeta B A distinguishedSource source target k g₂
            F hF bound hbound left‖ ^ 2) =
      ∫⁻ uv,
        ENNReal.ofReal
          ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier
              H N hN beta hbeta B distinguishedSource source target k g₂
              F left (A, uv)) ^ 2)
        ∂PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedBackgroundSourcePairMeasure
          H N hN beta hbeta B A distinguishedSource source k g₂ := by
  let μ :=
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedBackgroundSourcePairMeasure
      H N hN beta hbeta B A distinguishedSource source k g₂
  let R :=
    fun uv =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier
        H N hN beta hbeta B distinguishedSource source target k g₂
        F left (A, uv)
  let L :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeFixedBackgroundL2
      H N hN beta hbeta B A distinguishedSource source target k g₂
      F hF bound hbound left
  have hMem : MemLp R 2 μ := by
    simpa [R, μ] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnFixedBackground_memLp_two_of_bounded
        H N hN beta hbeta B A distinguishedSource source target k g₂
        F hF bound hbound left
  have hRep : (fun uv => L uv) =ᵐ[μ] R := by
    simpa [L, R, μ] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeFixedBackgroundL2_coeFn
        H N hN beta hbeta B A distinguishedSource source target k g₂
        F hF bound hbound left
  have hNorm :
      ‖L‖ ^ 2 = ∫ uv, (R uv) ^ 2 ∂μ := by
    rw [realL2_norm_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [hRep] with uv huv
    rw [huv]
    simp [Real.norm_eq_abs, sq_abs]
  have hSqInt : Integrable (fun uv => (R uv) ^ 2) μ := by
    simpa only [Pi.pow_apply] using hMem.integrable_sq
  have hOfReal :
      (∫⁻ uv, ENNReal.ofReal ((R uv) ^ 2) ∂μ) =
        ENNReal.ofReal (∫ uv, (R uv) ^ 2 ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal hSqInt
      (ae_of_all μ fun uv => sq_nonneg (R uv))).symm
  calc
    ENNReal.ofReal (‖L‖ ^ 2) =
        ENNReal.ofReal (∫ uv, (R uv) ^ 2 ∂μ) := by rw [hNorm]
    _ = ∫⁻ uv, ENNReal.ofReal ((R uv) ^ 2) ∂μ := hOfReal.symm

/-- The full source-pair second-mean RMS squared L2 norm is exactly its
pointwise square lower integral on the full source-pair/background law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2_norm_sq_ofReal_eq_lintegral
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2
            H N hN beta hbeta B distinguishedSource source target k g₂
            F hF bound hbound left‖ ^ 2) =
      ∫⁻ z,
        ENNReal.ofReal
          ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier
              H N hN beta hbeta B distinguishedSource source target k g₂
              F left z) ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
          H N hN beta hbeta B distinguishedSource source k g₂ := by
  let ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
      H N hN beta hbeta B distinguishedSource source k g₂
  let R :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier
      H N hN beta hbeta B distinguishedSource source target k g₂ F left
  let L :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2
      H N hN beta hbeta B distinguishedSource source target k g₂
      F hF bound hbound left
  have hMem : MemLp R 2 ν := by
    simpa [R, ν] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier_memLp_two_of_bounded
        H N hN beta hbeta B distinguishedSource source target k g₂
        F hF bound hbound left
  have hRep : (fun z => L z) =ᵐ[ν] R := by
    simpa [L, R, ν] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2_coeFn
        H N hN beta hbeta B distinguishedSource source target k g₂
        F hF bound hbound left
  have hNorm :
      ‖L‖ ^ 2 = ∫ z, (R z) ^ 2 ∂ν := by
    rw [realL2_norm_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [hRep] with z hz
    rw [hz]
    simp [Real.norm_eq_abs, sq_abs]
  have hSqInt : Integrable (fun z => (R z) ^ 2) ν := by
    simpa only [Pi.pow_apply] using hMem.integrable_sq
  have hOfReal :
      (∫⁻ z, ENNReal.ofReal ((R z) ^ 2) ∂ν) =
        ENNReal.ofReal (∫ z, (R z) ^ 2 ∂ν) :=
    (ofReal_integral_eq_lintegral_ofReal hSqInt
      (ae_of_all ν fun z => sq_nonneg (R z))).symm
  calc
    ENNReal.ofReal (‖L‖ ^ 2) =
        ENNReal.ofReal (∫ z, (R z) ^ 2 ∂ν) := by rw [hNorm]
    _ = ∫⁻ z, ENNReal.ofReal ((R z) ^ 2) ∂ν := hOfReal.symm

/-- At current values, the full source-pair law disintegrates exactly over the
fixed-right kernel-section background law and the fixed-background source-pair
fiber. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure_diagonalCurrentValues_lintegral_eq_fixedBackground
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (Phi :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (Matrix.specialUnitaryGroup (Fin N) ℂ ×
          Matrix.specialUnitaryGroup (Fin N) ℂ)) → ℝ≥0∞)
    (hPhi : Measurable Phi) :
    (∫⁻ z, Phi z
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
        H N hN beta hbeta C distinguishedSource source
        (C distinguishedSource) (C source)) =
      ∫⁻ A,
        ∫⁻ uv, Phi (A, uv)
          ∂PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedBackgroundSourcePairMeasure
            H N hN beta hbeta C A distinguishedSource source
            (C distinguishedSource) (C source)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta C := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
      H N hN beta hbeta C source distinguishedSource
      (C distinguishedSource) (C source)
  let κ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalIndependentPairKernel
      H N hN beta hbeta C source distinguishedSource source
      (C distinguishedSource) (C source)
  letI : IsProbabilityMeasure μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_isProbabilityMeasure
      H N hN beta hbeta C source distinguishedSource
      (C distinguishedSource) (C source)
  have hComp :
      (∫⁻ z, Phi z ∂μ ⊗ₘ κ) =
        ∫⁻ A, ∫⁻ uv, Phi (A, uv) ∂κ A ∂μ :=
    Measure.lintegral_compProd hPhi
  have hμ :
      μ =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta C := by
    simpa [μ] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_diagonalCurrentValues_eq_kernelSection
        H N hN beta hbeta C source distinguishedSource
  rw [hμ] at hComp
  simpa [
    μ, κ,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure,
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedBackgroundSourcePairMeasure] using hComp

/-- Exact Fubini bridge between the current-value fixed-background RMS norms
and the corresponding full source-pair RMS L2 norm. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeCurrentValueFixedBackgroundL2_norm_sq_lintegral_eq_fullL2_norm_sq_ofReal
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (∫⁻ A,
      ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeCurrentValueFixedBackgroundL2
            H N hN beta hbeta C A distinguishedSource source target
            F hF bound hbound C‖ ^ 2)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta C) =
      ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2
            H N hN beta hbeta C distinguishedSource source target
            (C distinguishedSource) (C source)
            F hF bound hbound C‖ ^ 2) := by
  let R :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier
      H N hN beta hbeta C distinguishedSource source target
      (C distinguishedSource) (C source) F C
  let Phi :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (Matrix.specialUnitaryGroup (Fin N) ℂ ×
          Matrix.specialUnitaryGroup (Fin N) ℂ)) → ℝ≥0∞ :=
    fun z => ENNReal.ofReal ((R z) ^ 2)
  have hRStrong : StronglyMeasurable R := by
    simpa [R] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier_stronglyMeasurable
        H N hN beta hbeta C distinguishedSource source target
        (C distinguishedSource) (C source) F hF C
  have hPhi : Measurable Phi :=
    ENNReal.continuous_ofReal.measurable.comp
      (hRStrong.measurable.pow_const 2)
  have hFubini :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure_diagonalCurrentValues_lintegral_eq_fixedBackground
      H N hN beta hbeta C distinguishedSource source Phi hPhi
  have hFixed :
      ∀ A,
        ENNReal.ofReal
            (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeCurrentValueFixedBackgroundL2
                H N hN beta hbeta C A distinguishedSource source target
                F hF bound hbound C‖ ^ 2) =
          ∫⁻ uv, Phi (A, uv)
            ∂PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedBackgroundSourcePairMeasure
              H N hN beta hbeta C A distinguishedSource source
              (C distinguishedSource) (C source) := by
    intro A
    simpa [
      Phi, R,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeCurrentValueFixedBackgroundL2] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeFixedBackgroundL2_norm_sq_ofReal_eq_lintegral
        H N hN beta hbeta C A distinguishedSource source target
        (C distinguishedSource) (C source)
        F hF bound hbound C
  have hFull :
      ENNReal.ofReal
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2
              H N hN beta hbeta C distinguishedSource source target
              (C distinguishedSource) (C source)
              F hF bound hbound C‖ ^ 2) =
        ∫⁻ z, Phi z
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
            H N hN beta hbeta C distinguishedSource source
            (C distinguishedSource) (C source) := by
    simpa [Phi, R] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2_norm_sq_ofReal_eq_lintegral
        H N hN beta hbeta C distinguishedSource source target
        (C distinguishedSource) (C source)
        F hF bound hbound C
  calc
    (∫⁻ A,
      ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeCurrentValueFixedBackgroundL2
            H N hN beta hbeta C A distinguishedSource source target
            F hF bound hbound C‖ ^ 2)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta C) =
      ∫⁻ A,
        ∫⁻ uv, Phi (A, uv)
          ∂PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedBackgroundSourcePairMeasure
            H N hN beta hbeta C A distinguishedSource source
            (C distinguishedSource) (C source)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta C := by
            apply lintegral_congr
            intro A
            exact hFixed A
    _ =
      ∫⁻ z, Phi z
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
          H N hN beta hbeta C distinguishedSource source
          (C distinguishedSource) (C source) := hFubini.symm
    _ =
      ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2
            H N hN beta hbeta C distinguishedSource source target
            (C distinguishedSource) (C source)
            F hF bound hbound C‖ ^ 2) := hFull.symm

end

end MGAP4D.MathlibAnalytic
