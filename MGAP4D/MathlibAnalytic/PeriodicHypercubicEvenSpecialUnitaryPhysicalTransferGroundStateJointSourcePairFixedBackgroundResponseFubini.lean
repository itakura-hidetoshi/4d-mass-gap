import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairFixedBackgroundRMSFubini
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairCurrentValueFixedBackgroundFiberL2
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairCanonicalTargetLawResponseL2
import MGAP4D.MathlibAnalytic.RealL2ExternalTensor
import Mathlib.Tactic

/-!
# Fixed-background response Fubini bridge

PR #4831 proves the exact full/fixed-background Fubini bridge for the
second-mean RMS amplitude.  The concrete target-law response lives on the
same source-pair carriers and admits the same exact disintegration.

This file proves:

1. the squared norm of the fixed-background response L2 vector is exactly the
   source-pair-fiber lower integral of the pointwise response square;
2. the squared norm of the full source-pair response L2 vector is exactly the
   corresponding full lower integral;
3. at current values, integrating the fixed-background response norm square
   over the fixed-right kernel-section outer law gives exactly the full
   source-pair response L2 norm square.

Thus, for fixed C,

  integral_A ofReal(||Response_fiber(A;source,target)||^2)
    = ofReal(||Response_full(source,target)||^2).

No inequality, coefficient, source summation, finite-cardinality factor,
factor two, or new probability law is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance fixedBackgroundResponseFubiniSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance fixedBackgroundResponseFubiniSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance fixedBackgroundResponseFubiniSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance fixedBackgroundResponseFubiniSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance fixedBackgroundResponseFubiniSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance fixedBackgroundResponseFubiniSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The fixed-background response squared L2 norm is exactly its pointwise
square lower integral on the source-pair fiber. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseFixedBackgroundL2_norm_sq_ofReal_eq_lintegral
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
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (center : ℝ) :
    ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseFixedBackgroundL2
            H N hN beta hbeta B A distinguishedSource source target k g₂
            F hF bound hbound left center‖ ^ 2) =
      ∫⁻ uv,
        ENNReal.ofReal
          ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnCarrier
              H N hN beta hbeta target source F left B distinguishedSource
              k g₂ center (A, uv)) ^ 2)
        ∂PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedBackgroundSourcePairMeasure
          H N hN beta hbeta B A distinguishedSource source k g₂ := by
  let μ :=
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedBackgroundSourcePairMeasure
      H N hN beta hbeta B A distinguishedSource source k g₂
  let R :=
    fun uv =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnCarrier
        H N hN beta hbeta target source F left B distinguishedSource
        k g₂ center (A, uv)
  let L :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseFixedBackgroundL2
      H N hN beta hbeta B A distinguishedSource source target k g₂
      F hF bound hbound left center
  have hMem : MemLp R 2 μ := by
    simpa [R, μ] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnFixedBackground_memLp_two_of_bounded
        H N hN beta hbeta B A distinguishedSource source target k g₂
        F hF bound hbound left center
  have hRep : (fun uv => L uv) =ᵐ[μ] R := by
    simpa [
      L, R, μ,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseFixedBackgroundL2] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnFixedBackground_memLp_two_of_bounded
        H N hN beta hbeta B A distinguishedSource source target k g₂
        F hF bound hbound left center).coeFn_toLp
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

/-- The full source-pair response squared L2 norm is exactly its pointwise
square lower integral on the full source-pair/background law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2_norm_sq_ofReal_eq_lintegral
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
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (center : ℝ) :
    ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
            H N hN beta hbeta B distinguishedSource source target k g₂
            F hF bound hbound left center‖ ^ 2) =
      ∫⁻ z,
        ENNReal.ofReal
          ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnCarrier
              H N hN beta hbeta target source F left B distinguishedSource
              k g₂ center z) ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
          H N hN beta hbeta B distinguishedSource source k g₂ := by
  let ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
      H N hN beta hbeta B distinguishedSource source k g₂
  let R :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnCarrier
      H N hN beta hbeta target source F left B distinguishedSource
      k g₂ center
  let L :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
      H N hN beta hbeta B distinguishedSource source target k g₂
      F hF bound hbound left center
  have hMem : MemLp R 2 ν := by
    simpa [R, ν] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnCarrier_memLp_two_of_bounded
        H N hN beta hbeta B distinguishedSource source target k g₂
        F hF bound hbound left center
  have hRep : (fun z => L z) =ᵐ[ν] R := by
    simpa [L, R, ν] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2_coeFn
        H N hN beta hbeta B distinguishedSource source target k g₂
        F hF bound hbound left center
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

/-- Exact current-value Fubini bridge for the concrete target-law response. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseCurrentValueFixedBackgroundL2_norm_sq_lintegral_eq_fullL2_norm_sq_ofReal
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
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseCurrentValueFixedBackgroundL2
            H N hN beta hbeta C A distinguishedSource source target
            F hF bound hbound C‖ ^ 2)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta C) =
      ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
            H N hN beta hbeta C distinguishedSource source target
            (C distinguishedSource) (C source)
            F hF bound hbound C 0‖ ^ 2) := by
  let R :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnCarrier
      H N hN beta hbeta target source F C C distinguishedSource
      (C distinguishedSource) (C source) 0
  let Phi :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (Matrix.specialUnitaryGroup (Fin N) ℂ ×
          Matrix.specialUnitaryGroup (Fin N) ℂ)) → ℝ≥0∞ :=
    fun z => ENNReal.ofReal ((R z) ^ 2)
  have hRStrong : StronglyMeasurable R := by
    simpa [R] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnCarrier_stronglyMeasurable
        H N hN beta hbeta C distinguishedSource source target
        (C distinguishedSource) (C source)
        F hF C 0
  have hPhi : Measurable Phi :=
    ENNReal.continuous_ofReal.measurable.comp
      (hRStrong.measurable.pow_const 2)
  have hFubini :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure_diagonalCurrentValues_lintegral_eq_fixedBackground
      H N hN beta hbeta C distinguishedSource source Phi hPhi
  have hFixed :
      ∀ A,
        ENNReal.ofReal
            (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseCurrentValueFixedBackgroundL2
                H N hN beta hbeta C A distinguishedSource source target
                F hF bound hbound C‖ ^ 2) =
          ∫⁻ uv, Phi (A, uv)
            ∂PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedBackgroundSourcePairMeasure
              H N hN beta hbeta C A distinguishedSource source
              (C distinguishedSource) (C source) := by
    intro A
    simpa [
      Phi, R,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseCurrentValueFixedBackgroundL2] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseFixedBackgroundL2_norm_sq_ofReal_eq_lintegral
        H N hN beta hbeta C A distinguishedSource source target
        (C distinguishedSource) (C source)
        F hF bound hbound C 0
  have hFull :
      ENNReal.ofReal
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
              H N hN beta hbeta C distinguishedSource source target
              (C distinguishedSource) (C source)
              F hF bound hbound C 0‖ ^ 2) =
        ∫⁻ z, Phi z
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
            H N hN beta hbeta C distinguishedSource source
            (C distinguishedSource) (C source) := by
    simpa [Phi, R] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2_norm_sq_ofReal_eq_lintegral
        H N hN beta hbeta C distinguishedSource source target
        (C distinguishedSource) (C source)
        F hF bound hbound C 0
  calc
    (∫⁻ A,
      ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseCurrentValueFixedBackgroundL2
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
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
            H N hN beta hbeta C distinguishedSource source target
            (C distinguishedSource) (C source)
            F hF bound hbound C 0‖ ^ 2) := hFull.symm

end

end MGAP4D.MathlibAnalytic
