import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTwoWilsonPosteriorSourceExpectationGapV5_GI
import Mathlib.Tactic

/-!
# P4-Q2-GJ: sharpen genuine original Wilson source response RMS using its exact gap

GA's earlier positive-beta posterior left-row Haar distance was bounded
BELOW by beta^2 exp(-32 beta) V_SU2, and GB/GC/GD/GE applied that lower
constant to the exact signed physical source projection.

But the original Cauchy-Schwarz theorem of GB controls
   Q(z) * alpha(z)^2
where Q(z) is the EXACT squared Haar L² distance between the two
genuine normalized Wilson conditional posterior density rows.

GI proved the real two-original-posterior signed-source EXPECTATION
gap Delta(z) equals Q(z)*alpha(z). The SHARP local certificate is

  M2_original_Wilson(z)
       >= exp(-16 beta) * Delta(z) * alpha(z)
        = exp(-16 beta) * Q(z) * alpha(z)^2 >= 0.

This retains the true full Q(z) rather than discarding it to the
universal beta² floor. Crucially M2 uses the ORIGINAL interacting
Wilson INNER posterior; Haar occurs only as the exact Cauchy-Schwarz
reference and the outer pair-Haar context.

Prove the gap–projection product nonnegative and automatically
pair-Haar-integrable using GD genuine measurability, FG integrated
physical conditional RMS, and the improved pointwise bound. Then
integrate to an exact physical original Wilson link-mass lower bound.

This is a genuine quantitative finite-volume improvement, but no
physical-source detection existence, source-frame positive constant,
H-/scale-uniform spatial sum, H1-C3 closure or continuum gap is claimed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1700000
set_option synthInstance.maxHeartbeats 650000

local instance p4Q2GJ_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2GJ_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2GJ_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2GJ_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2GJ_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- Nonnegative EXACT Wilson two-posterior signed response gap paired
with its original physical source projection, since it equals the true
Wilson density-row Haar square times the original source alpha². -/
theorem p4Q2GJ_originalWilsonSignedGap_mul_projection_nonneg
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    0 ≤
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H beta (le_of_lt hbeta) f e z *
      p4Q2GB_originalPhysicalSourcePosteriorContrastProjection
        H beta (le_of_lt hbeta) f e z := by
  let Q := p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
    H beta (le_of_lt hbeta) z.2 e
  let alpha := p4Q2GB_originalPhysicalSourcePosteriorContrastProjection
    H beta (le_of_lt hbeta) f e z
  have hQ : 0 ≤ Q := (p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq_pos
    H beta hbeta z.2 e).le
  calc
    (0 : ℝ) ≤ Q * alpha ^ 2 := mul_nonneg hQ (sq_nonneg _)
    _ = p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H beta (le_of_lt hbeta) f e z * alpha := by
      rw [p4Q2GI_originalWilsonSignedExpectationGap_eq_projection_mul_variance
        H beta hbeta f e z]
      ring

/-- Original TRUE interacting Wilson conditional RMS retains the SHARP
density-row L² factor Q(z) instead of replacing Q(z) by GA's beta²
uniform floor.  The right side is the ACTUAL difference of two true
Wilson conditional expectations of the unchanged signed physical FF
response, times its actual source projection coefficient. -/
theorem p4Q2GJ_originalWilsonConditionalRMS_ge_actualSignedGapProjection
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    Real.exp (-16 * beta) *
      (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H beta (le_of_lt hbeta) f e z *
       p4Q2GB_originalPhysicalSourcePosteriorContrastProjection
        H beta (le_of_lt hbeta) f e z) ≤
      p4Q2FG_originalWilsonRelativeResponseConditionalSquare
        H 2 (by norm_num) beta (le_of_lt hbeta) f e z := by
  let μ : Measure (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
    normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)
  let B := p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
    H 2 (by norm_num) beta (le_of_lt hbeta) f e
  let R : Matrix.specialUnitaryGroup (Fin 2) ℂ → ℝ := fun g => B (z,g)
  let P0 : Matrix.specialUnitaryGroup (Fin 2) ℂ → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
      H 2 (by norm_num) beta (le_of_lt hbeta)
      (originalWilsonExplicitIdentityBoundary H) z.2 e
  let P1 : Matrix.specialUnitaryGroup (Fin 2) ℂ → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
      H 2 (by norm_num) beta (le_of_lt hbeta)
      (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) z.2 e
  let D := p4Q2GB_originalWilsonPosteriorLeftDensityContrast
    H beta (le_of_lt hbeta) z.2 e
  let Q := p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
    H beta (le_of_lt hbeta) z.2 e
  let alpha := p4Q2GB_originalPhysicalSourcePosteriorContrastProjection
    H beta (le_of_lt hbeta) f e z
  let Delta := p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
    H beta (le_of_lt hbeta) f e z
  have hR : Continuous R :=
    B.continuous.comp (continuous_const.prodMk continuous_id)
  have hP0 : Continuous P0 := by
    change Continuous
      (continuousNormalizedExp μ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
          H 2 (by norm_num) beta (le_of_lt hbeta)
          (originalWilsonExplicitIdentityBoundary H) z.2 e))
    exact continuous_continuousNormalizedExp μ _
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
        H 2 (by norm_num) beta (le_of_lt hbeta)
        (originalWilsonExplicitIdentityBoundary H) z.2 e)
  have hP1 : Continuous P1 := by
    change Continuous
      (continuousNormalizedExp μ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
          H 2 (by norm_num) beta (le_of_lt hbeta)
          (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) z.2 e))
    exact continuous_continuousNormalizedExp μ _
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
        H 2 (by norm_num) beta (le_of_lt hbeta)
        (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) z.2 e)
  have hD : Continuous D := by
    change Continuous (fun g => P0 g - P1 g)
    exact hP0.sub hP1
  have hQPos : 0 < Q :=
    p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq_pos
      H beta hbeta z.2 e
  have hProjection : Q * alpha ^ 2 ≤ ∫ g, (R g) ^ 2 ∂μ := by
    convert p4Q2GB_continuousProbability_projection_sq_le
      μ R D hR hD (by change 0 < Q; exact hQPos) using 1
  have hHaarLower :
      Real.exp (-16 * beta) *
        p4Q2FM_originalWilsonRelativeSignedHaarSquaredMoment
          H 2 (by norm_num) beta (le_of_lt hbeta) f e z ≤
      p4Q2FG_originalWilsonRelativeResponseConditionalSquare
        H 2 (by norm_num) beta (le_of_lt hbeta) f e z :=
    (p4Q2FM_originalWilsonConditionalRMS_real_haar_sandwich
      H 2 (by norm_num) beta (le_of_lt hbeta) f e z).1
  have hDelta : Delta = alpha * Q :=
    p4Q2GI_originalWilsonSignedExpectationGap_eq_projection_mul_variance
      H beta hbeta f e z
  change Real.exp (-16 * beta) * (Delta * alpha) ≤
    p4Q2FG_originalWilsonRelativeResponseConditionalSquare
      H 2 (by norm_num) beta (le_of_lt hbeta) f e z
  calc
    Real.exp (-16 * beta) * (Delta * alpha) =
        Real.exp (-16 * beta) * (Q * alpha ^ 2) := by
      rw [hDelta]
      ring
    _ ≤ Real.exp (-16 * beta) * (∫ g, (R g) ^ 2 ∂μ) :=
      mul_le_mul_of_nonneg_left hProjection (Real.exp_pos _).le
    _ = Real.exp (-16 * beta) *
        p4Q2FM_originalWilsonRelativeSignedHaarSquaredMoment
          H 2 (by norm_num) beta (le_of_lt hbeta) f e z := rfl
    _ ≤ _ := hHaarLower

/-- The true Wilson signed expectation gap–projection product is
automatically pair-Haar integrable: its nonnegative value is
dominated by the already integrable original physical conditional
RMS divided by the positive FK posterior density floor. -/
theorem p4Q2GJ_originalWilsonSignedGapProjection_pairHaar_integrable
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    Integrable
      (fun z =>
        p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H beta (le_of_lt hbeta) f e z *
        p4Q2GB_originalPhysicalSourcePosteriorContrastProjection
          H beta (le_of_lt hbeta) f e z)
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  let alpha := p4Q2GB_originalPhysicalSourcePosteriorContrastProjection
    H beta (le_of_lt hbeta) f e
  let Delta := p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
    H beta (le_of_lt hbeta) f e
  let Q := fun z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 =>
      p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
        H beta (le_of_lt hbeta) z.2 e
  let G := fun z => Delta z * alpha z
  let M := p4Q2FG_originalWilsonRelativeResponseConditionalSquare
    H 2 (by norm_num) beta (le_of_lt hbeta) f e
  let c := Real.exp (-16 * beta)
  have hc : 0 < c := Real.exp_pos _
  have hAlphaMeas : Measurable alpha :=
    p4Q2GD_originalPhysicalSourceContrastProjection_measurable
      H beta (le_of_lt hbeta) f e
  have hQMeas : Measurable Q :=
    (p4Q2GD_originalWilsonPosteriorContrastHaarSq_measurable
      H beta (le_of_lt hbeta) e).comp measurable_snd
  have hDeltaMeas : Measurable Delta := by
    convert (hAlphaMeas.mul hQMeas) using 1
    funext z
    exact (p4Q2GI_originalWilsonSignedExpectationGap_eq_projection_mul_variance
      H beta hbeta f e z).symm
  have hGMeas : AEStronglyMeasurable G μ :=
    (hDeltaMeas.mul hAlphaMeas).aestronglyMeasurable
  have hMInt : Integrable M μ :=
    p4Q2FG_originalWilsonRelativeResponseConditionalSquare_pairHaar_integrable
      H 2 (by norm_num) beta (le_of_lt hbeta) f e
  have hBoundInt : Integrable (fun z => M z / c) μ :=
    hMInt.div_const c
  change Integrable G μ
  apply Integrable.mono' hBoundInt hGMeas
  filter_upwards with z
  have hPoint : c * G z ≤ M z := by
    exact p4Q2GJ_originalWilsonConditionalRMS_ge_actualSignedGapProjection
      H beta hbeta f e z
  have hBound : G z ≤ M z / c := by
    apply (le_div_iff₀ hc).2
    calc
      G z * c = c * G z := mul_comm _ _
      _ ≤ M z := hPoint
  have hMnonneg : 0 ≤ M z :=
    p4Q2FG_originalWilsonRelativeResponseConditionalSquare_nonneg
      H 2 (by norm_num) beta (le_of_lt hbeta) f e z
  have hDivnonneg : 0 ≤ M z / c := div_nonneg hMnonneg hc.le
  have hGnonneg : 0 ≤ G z :=
    p4Q2GJ_originalWilsonSignedGap_mul_projection_nonneg
      H beta hbeta f e z
  change ‖G z‖ ≤ M z / c
  rw [Real.norm_eq_abs, abs_of_nonneg hGnonneg]
  exact hBound

/-- Exact true-Wilson two-posterior signed-source expectation gap
projection mass integrated over the original outer pair-Haar context.
The sharper comparison depends on the actual original source, and
does not postulate a coefficient-frame lower bound. -/
noncomputable def p4Q2GJ_originalWilsonSignedGapProjectionLinkMean
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  ∫ z,
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H beta hbeta f e z *
    p4Q2GB_originalPhysicalSourcePosteriorContrastProjection
      H beta hbeta f e z
    ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2

/-- Integrated original Wilson physical conditional RMS strictly retains
its TRUE density-row factor Q rather than only GA's beta² lower floor.
Every required source/expectation integrability was proved above. -/
theorem p4Q2GJ_originalWilsonLinkRMS_ge_sharpSignedGapProjection
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    Real.exp (-16 * beta) *
      p4Q2GJ_originalWilsonSignedGapProjectionLinkMean
        H beta (le_of_lt hbeta) f e ≤
      p4Q2FH_originalWilsonConditionalRMSLinkMean
        H 2 (by norm_num) beta (le_of_lt hbeta) f e := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  let G := fun z =>
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H beta (le_of_lt hbeta) f e z *
    p4Q2GB_originalPhysicalSourcePosteriorContrastProjection
      H beta (le_of_lt hbeta) f e z
  let M := p4Q2FG_originalWilsonRelativeResponseConditionalSquare
    H 2 (by norm_num) beta (le_of_lt hbeta) f e
  have hGInt : Integrable G μ :=
    p4Q2GJ_originalWilsonSignedGapProjection_pairHaar_integrable
      H beta hbeta f e
  have hMInt : Integrable M μ :=
    p4Q2FG_originalWilsonRelativeResponseConditionalSquare_pairHaar_integrable
      H 2 (by norm_num) beta (le_of_lt hbeta) f e
  change Real.exp (-16 * beta) * (∫ z, G z ∂μ) ≤
    ∫ z, M z ∂μ
  calc
    Real.exp (-16 * beta) * (∫ z, G z ∂μ) =
        ∫ z, Real.exp (-16 * beta) * G z ∂μ := by
      rw [integral_const_mul]
    _ ≤ ∫ z, M z ∂μ := by
      apply integral_mono (hGInt.const_mul _) hMInt
      intro z
      exact p4Q2GJ_originalWilsonConditionalRMS_ge_actualSignedGapProjection
        H beta hbeta f e z

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GJ_originalWilsonSignedGap_mul_projection_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GJ_originalWilsonConditionalRMS_ge_actualSignedGapProjection
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GJ_originalWilsonSignedGapProjection_pairHaar_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GJ_originalWilsonLinkRMS_ge_sharpSignedGapProjection
