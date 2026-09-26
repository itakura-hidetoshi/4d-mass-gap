import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairCanonicalTargetLawRMSAmplitudeL2
import Mathlib.Tactic

/-!
# Fixed-background source-pair fiber L2

The source-specific carrier from PR #4724 integrates both the outer background
and the two conditionally independent source-link samples.  That carrier is
appropriate for the configuration-independent pin-free coefficient, but the
final transpose Schur receiver of PR #4773 must retain the actual
background-dependent physical envelope

  K_A(target,source).

This file therefore slices the source-pair construction at a fixed outer
background A.  The remaining carrier is exactly the conditionally independent
pair law of the source link at A.  It is target-independent, so every response
indexed by target for a fixed source lives in one common L2 space.

The PR #4775 pointwise estimate then lifts without loss to

  ||Response_A(source,target)||_2
    <= K_A(target,source) * ||RMS_A(source,target)||_2.

No background supremum, pin-free replacement, factor two, or finite-cardinality
factor is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

local instance fixedBackgroundFiberL2SpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance fixedBackgroundFiberL2SpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance fixedBackgroundFiberL2SpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance fixedBackgroundFiberL2SpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance fixedBackgroundFiberL2SpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance fixedBackgroundFiberL2SpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The conditionally independent source-pair law at one fixed outer
background.  The target response index does not occur in this measure. -/
abbrev
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedBackgroundSourcePairMeasure
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Measure
      (Matrix.specialUnitaryGroup (Fin N) ℂ ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalIndependentPairKernel
    H N hN beta hbeta B source distinguishedSource source k g₂ A

/-- Fixed-background source-pair L2 carrier.  For fixed A and source this type
is common to all response targets. -/
abbrev
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedBackgroundSourcePairL2
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) : Type :=
  Lp ℝ 2
    (PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedBackgroundSourcePairMeasure
      H N hN beta hbeta B A distinguishedSource source k g₂)

/-- At a fixed background the concrete target-law response remains strongly
measurable as a function of the two source-link samples. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnFixedBackground_stronglyMeasurable
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (center : ℝ) :
    StronglyMeasurable
      (fun uv =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnCarrier
          H N hN beta hbeta target source F left B distinguishedSource
          k g₂ center (A, uv)) := by
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnCarrier_stronglyMeasurable
      H N hN beta hbeta B distinguishedSource source target k g₂
      F hF left center).comp_measurable
      (measurable_const.prodMk measurable_id)

/-- The exact RMS amplitude likewise remains strongly measurable after fixing
the outer background. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawRMSAmplitudeOnFixedBackground_stronglyMeasurable
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (center : ℝ) :
    StronglyMeasurable
      (fun uv =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawRMSAmplitudeOnCarrier
          H N hN beta hbeta target source F left B distinguishedSource
          k g₂ center (A, uv)) := by
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawRMSAmplitudeOnCarrier_stronglyMeasurable
      H N hN beta hbeta B distinguishedSource source target k g₂
      F hF left center).comp_measurable
      (measurable_const.prodMk measurable_id)

/-- Fixed-background response section belongs to the source-pair fiber L2
carrier on the bounded-concrete core. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnFixedBackground_memLp_two_of_bounded
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
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (center : ℝ) :
    MemLp
      (fun uv =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnCarrier
          H N hN beta hbeta target source F left B distinguishedSource
          k g₂ center (A, uv))
      2
      (PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedBackgroundSourcePairMeasure
        H N hN beta hbeta B A distinguishedSource source k g₂) := by
  exact
    MemLp.of_bound
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnFixedBackground_stronglyMeasurable
        H N hN beta hbeta B A distinguishedSource source target k g₂
        F hF left center).aestronglyMeasurable
      (2 * (|bound| + |center|))
      (Filter.Eventually.of_forall fun uv =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnCarrier_norm_le
          H N hN beta hbeta B distinguishedSource source target k g₂
          F bound hbound left center (A, uv))

/-- Fixed-background RMS section belongs to the same source-pair fiber L2
carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawRMSAmplitudeOnFixedBackground_memLp_two_of_bounded
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
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (center : ℝ) :
    MemLp
      (fun uv =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawRMSAmplitudeOnCarrier
          H N hN beta hbeta target source F left B distinguishedSource
          k g₂ center (A, uv))
      2
      (PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedBackgroundSourcePairMeasure
        H N hN beta hbeta B A distinguishedSource source k g₂) := by
  exact
    MemLp.of_bound
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawRMSAmplitudeOnFixedBackground_stronglyMeasurable
        H N hN beta hbeta B A distinguishedSource source target k g₂
        F hF left center).aestronglyMeasurable
      (2 * (|bound| + |center|))
      (Filter.Eventually.of_forall fun uv =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawRMSAmplitudeOnCarrier_norm_le
          H N hN beta hbeta B distinguishedSource source target k g₂
          F hF bound hbound left center (A, uv))

/-- Concrete target-law response as a vector in the fixed-background
source-specific L2 carrier. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseFixedBackgroundL2
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
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (center : ℝ) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedBackgroundSourcePairL2
      H N hN beta hbeta B A distinguishedSource k g₂ source :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnFixedBackground_memLp_two_of_bounded
    H N hN beta hbeta B A distinguishedSource source target k g₂
    F hF bound hbound left center).toLp
      (fun uv =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnCarrier
          H N hN beta hbeta target source F left B distinguishedSource
          k g₂ center (A, uv))

/-- Exact RMS amplitude as a vector in the same fixed-background
source-specific L2 carrier. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawRMSAmplitudeFixedBackgroundL2
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
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (center : ℝ) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedBackgroundSourcePairL2
      H N hN beta hbeta B A distinguishedSource k g₂ source :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawRMSAmplitudeOnFixedBackground_memLp_two_of_bounded
    H N hN beta hbeta B A distinguishedSource source target k g₂
    F hF bound hbound left center).toLp
      (fun uv =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawRMSAmplitudeOnCarrier
          H N hN beta hbeta target source F left B distinguishedSource
          k g₂ center (A, uv))

/-- Sharp fixed-background actual-envelope L2 response estimate.

Because A is fixed before forming the L2 norm, K_A(target,source) is a scalar
and factors through the norm without any replacement by K_pin. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseFixedBackgroundL2_norm_le_physicalEnvelope_mul_rmsAmplitudeFixedBackgroundL2_norm
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
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (center : ℝ) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseFixedBackgroundL2
        H N hN beta hbeta B A distinguishedSource source target k g₂
        F hF bound hbound left center‖ ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
        H N hN beta hbeta A).influence target source *
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawRMSAmplitudeFixedBackgroundL2
        H N hN beta hbeta B A distinguishedSource source target k g₂
        F hF bound hbound left center‖ := by
  let μ :=
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedBackgroundSourcePairMeasure
      H N hN beta hbeta B A distinguishedSource source k g₂
  let response :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseFixedBackgroundL2
      H N hN beta hbeta B A distinguishedSource source target k g₂
      F hF bound hbound left center
  let amplitude :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawRMSAmplitudeFixedBackgroundL2
      H N hN beta hbeta B A distinguishedSource source target k g₂
      F hF bound hbound left center
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
            k g₂ center (A, uv)) := by
    simpa [response, μ,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseFixedBackgroundL2] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnFixedBackground_memLp_two_of_bounded
        H N hN beta hbeta B A distinguishedSource source target k g₂
        F hF bound hbound left center).coeFn_toLp
  have hAmplitudeRep :
      (fun uv => amplitude uv) =ᵐ[μ]
        (fun uv =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawRMSAmplitudeOnCarrier
            H N hN beta hbeta target source F left B distinguishedSource
            k g₂ center (A, uv)) := by
    simpa [amplitude, μ,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawRMSAmplitudeFixedBackgroundL2] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawRMSAmplitudeOnFixedBackground_memLp_two_of_bounded
        H N hN beta hbeta B A distinguishedSource source target k g₂
        F hF bound hbound left center).coeFn_toLp
  have hSmul := Lp.coeFn_smul (K.influence target source) amplitude
  have hPoint :
      ∀ᵐ uv ∂μ,
        ‖response uv‖ ≤ ‖(K.influence target source • amplitude) uv‖ := by
    filter_upwards [hResponseRep, hAmplitudeRep, hSmul] with uv hR hAmp hS
    rw [hR, hS]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hAmp]
    have hRaw :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnCarrier_abs_le_physicalEnvelope_mul_rmsAmplitude_of_bounded
        N hN s hs beta hbeta hcut H target source F hF bound hbound
        left B distinguishedSource k g₂ center (A, uv)
    have hAmp0 :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawRMSAmplitudeOnCarrier_nonneg
        H N hN beta hbeta B distinguishedSource source target k g₂
        F left center (A, uv)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have hProd0 :
        0 ≤
          K.influence target source *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawRMSAmplitudeOnCarrier
              H N hN beta hbeta target source F left B distinguishedSource
              k g₂ center (A, uv) :=
      mul_nonneg hK0 hAmp0
    rw [abs_of_nonneg hProd0]
    simpa [K] using hRaw
  calc
    ‖response‖ ≤ ‖K.influence target source • amplitude‖ :=
      Lp.norm_le_norm_of_ae_le hPoint
    _ = K.influence target source * ‖amplitude‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hK0]
    _ = _ := rfl

end

end MGAP4D.MathlibAnalytic
