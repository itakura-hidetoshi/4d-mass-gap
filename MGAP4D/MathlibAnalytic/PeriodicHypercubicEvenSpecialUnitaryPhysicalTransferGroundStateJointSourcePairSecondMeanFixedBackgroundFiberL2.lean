import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundFiberL2
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairSecondMeanRMSL2
import Mathlib.Tactic

/-!
# Second-mean RMS on the fixed-background source-pair fiber

PR #4820 slices the source-pair carrier before the outer background is
integrated, retaining the actual background-dependent influence coefficient
`K_A(target,source)`.

The final RMS authority, however, is not the fixed scalar-center amplitude.
PR #4800 replaces that temporary center by the actual second target-law fiber
mean pointwise.  This file performs the same fixed-background slicing for that
second-mean RMS.

For one fixed outer background `A`, the source-pair carrier remains
target-independent and the sharp response estimate is

  ||Response_A(source,target)||_2
    <= K_A(target,source) * ||RMS2_A(source,target)||_2.

Thus the actual physical envelope survives together with the final
second-law-mean centering.  No pin-free replacement, fixed-center fallback,
factor two, background supremum, or finite-cardinality factor is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

local instance secondMeanFixedBackgroundFiberL2SpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance secondMeanFixedBackgroundFiberL2SpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance secondMeanFixedBackgroundFiberL2SpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance secondMeanFixedBackgroundFiberL2SpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance secondMeanFixedBackgroundFiberL2SpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance secondMeanFixedBackgroundFiberL2SpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Restrict the final pointwise-second-mean RMS amplitude from PR #4800 to
one fixed outer background. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnFixedBackground_stronglyMeasurable
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    StronglyMeasurable
      (fun uv =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier
          H N hN beta hbeta B distinguishedSource source target k g₂
          F left (A, uv)) := by
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier_stronglyMeasurable
      H N hN beta hbeta B distinguishedSource source target k g₂
      F hF left).comp_measurable
      (measurable_const.prodMk measurable_id)

/-- The fixed-background second-mean RMS is in L2 on the bounded-concrete
core. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnFixedBackground_memLp_two_of_bounded
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
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
    MemLp
      (fun uv =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier
          H N hN beta hbeta B distinguishedSource source target k g₂
          F left (A, uv))
      2
      (PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedBackgroundSourcePairMeasure
        H N hN beta hbeta B A distinguishedSource source k g₂) := by
  exact
    MemLp.of_bound
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnFixedBackground_stronglyMeasurable
        H N hN beta hbeta B A distinguishedSource source target k g₂
        F hF left).aestronglyMeasurable
      (4 * |bound|)
      (Filter.Eventually.of_forall fun uv =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier_norm_le
          H N hN beta hbeta B distinguishedSource source target k g₂
          F hF bound hbound left (A, uv))

/-- Final second-law-mean RMS amplitude as a vector in the fixed-background
source-specific L2 carrier from PR #4820. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeFixedBackgroundL2
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
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
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedBackgroundSourcePairL2
      H N hN beta hbeta B A distinguishedSource k g₂ source :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnFixedBackground_memLp_two_of_bounded
    H N hN beta hbeta B A distinguishedSource source target k g₂
    F hF bound hbound left).toLp
      (fun uv =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier
          H N hN beta hbeta B distinguishedSource source target k g₂
          F left (A, uv))

/-- The fixed-background L2 vector has the actual second-mean RMS as its a.e.
representative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeFixedBackgroundL2_coeFn
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
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
    (fun uv =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeFixedBackgroundL2
        H N hN beta hbeta B A distinguishedSource source target k g₂
        F hF bound hbound left uv) =ᵐ[
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedBackgroundSourcePairMeasure
        H N hN beta hbeta B A distinguishedSource source k g₂]
      (fun uv =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier
          H N hN beta hbeta B distinguishedSource source target k g₂
          F left (A, uv)) := by
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnFixedBackground_memLp_two_of_bounded
      H N hN beta hbeta B A distinguishedSource source target k g₂
      F hF bound hbound left).coeFn_toLp

/-- Sharp actual-envelope response estimate with the final second-law-mean RMS
on the fixed-background source-pair fiber.

The response is represented at reference center zero; center-independence from
PR #4778 makes this compatible with the pointwise second-law mean used for the
RMS amplitude. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseFixedBackgroundL2_norm_le_physicalEnvelope_mul_secondMeanRMSAmplitudeFixedBackgroundL2_norm
    (N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
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
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseFixedBackgroundL2
        H N hN beta hbeta B A distinguishedSource source target k g₂
        F hF bound hbound left 0‖ ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
        H N hN beta hbeta A).influence target source *
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeFixedBackgroundL2
        H N hN beta hbeta B A distinguishedSource source target k g₂
        F hF bound hbound left‖ := by
  let μ :=
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedBackgroundSourcePairMeasure
      H N hN beta hbeta B A distinguishedSource source k g₂
  let response :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseFixedBackgroundL2
      H N hN beta hbeta B A distinguishedSource source target k g₂
      F hF bound hbound left 0
  let amplitude :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeFixedBackgroundL2
      H N hN beta hbeta B A distinguishedSource source target k g₂
      F hF bound hbound left
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
      H N hN beta hbeta A
  have hK0 : 0 ≤ K.influence target source :=
    K.influence_nonneg target source
  have hResponseRep :
      (fun uv => response uv) =ᵐ[μ]
        (fun uv =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnCarrier
            H N hN beta hbeta target source F left B distinguishedSource
            k g₂ 0 (A, uv)) := by
    simpa [response, μ,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseFixedBackgroundL2] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnFixedBackground_memLp_two_of_bounded
        H N hN beta hbeta B A distinguishedSource source target k g₂
        F hF bound hbound left 0).coeFn_toLp
  have hAmplitudeRep :
      (fun uv => amplitude uv) =ᵐ[μ]
        (fun uv =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier
            H N hN beta hbeta B distinguishedSource source target k g₂
            F left (A, uv)) := by
    simpa [amplitude, μ,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeFixedBackgroundL2] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnFixedBackground_memLp_two_of_bounded
        H N hN beta hbeta B A distinguishedSource source target k g₂
        F hF bound hbound left).coeFn_toLp
  have hSmul := Lp.coeFn_smul (K.influence target source) amplitude
  have hPoint :
      ∀ᵐ uv ∂μ,
        ‖response uv‖ ≤ ‖(K.influence target source • amplitude) uv‖ := by
    filter_upwards [hResponseRep, hAmplitudeRep, hSmul] with uv hR hAmp hS
    rw [hR, hS]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hAmp]
    have hRaw :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnCarrier_abs_le_physicalEnvelope_mul_rmsAmplitude_secondFiberMean_of_bounded
        N hN s hs beta hbeta hcut H target source F hF bound hbound
        left B distinguishedSource k g₂ 0 (A, uv)
    have hAmp0 :
        0 ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier
            H N hN beta hbeta B distinguishedSource source target k g₂
            F left (A, uv) := by
      unfold
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawRMSAmplitudeOnCarrier_nonneg
          H N hN beta hbeta B distinguishedSource source target k g₂
          F left
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondFiberMeanOnCarrier
            H N hN beta hbeta B distinguishedSource source target k g₂
            F left (A, uv))
          (A, uv)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have hProd0 :
        0 ≤
          K.influence target source *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier
              H N hN beta hbeta B distinguishedSource source target k g₂
              F left (A, uv) :=
      mul_nonneg hK0 hAmp0
    rw [abs_of_nonneg hProd0]
    simpa [
      K,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier] using hRaw
  calc
    ‖response‖ ≤ ‖K.influence target source • amplitude‖ :=
      Lp.norm_le_norm_of_ae_le hPoint
    _ = K.influence target source * ‖amplitude‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hK0]
    _ = _ := rfl

end

end MGAP4D.MathlibAnalytic
