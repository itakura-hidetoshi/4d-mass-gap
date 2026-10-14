import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPosteriorUniformLeftHaarL2FloorV5_GA
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalConditionalRMSRealHaarSandwichV5_FM
import Mathlib.Tactic

/-!
# P4-Q2-GB: genuine Wilson source/contrast projection, first bridge

GA supplies a uniformly positive HAAR squared separation between two
normalized genuine Wilson posterior densities for distinct LEFT endpoints.
FM bounds the original FG conditional signed physical-source response
RMS from below by the HAAR squared moment of the SAME genuine response.

Here the Hilbert-space Cauchy-Schwarz inequality identifies an explicit
source-dependent projection coefficient against the GA posterior
contrast. No lower bound on this physical source coefficient is assumed.

The conditional Wilson measure is NEVER substituted by independent Haar.
For beta>0 each pointwise true physical conditional RMS obeys

 exp(-16 beta) * [beta^2 * exp(-32 beta) * V_SU2] * alpha(e,f,z)^2
   <= M2_original_Wilson(e,f,z).

This is not yet a volume-uniform coercive frame theorem: alpha may vanish
for particular physical sources. No H1-C3 closure or continuum gap is claimed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators ComplexConjugate

noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 700000

local instance p4Q2GB_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2GB_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2GB_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2GB_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2GB_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- Exact compact real L² one-dimensional projection inequality.
Proved from mathlib's genuine real Hilbert-space Cauchy-Schwarz, not
by an abstractly assumed frame bound or pointwise Haar atoms. -/
theorem p4Q2GB_continuousProbability_projection_sq_le
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (R D : X → ℝ) (hR : Continuous R) (hD : Continuous D)
    (hQ : 0 < ∫ x, (D x) ^ 2 ∂μ) :
    (∫ x, (D x) ^ 2 ∂μ) *
        ((∫ x, R x * D x ∂μ) / (∫ x, (D x) ^ 2 ∂μ)) ^ 2 ≤
      ∫ x, (R x) ^ 2 ∂μ := by
  let F : C(X, ℝ) := ⟨R, hR⟩
  let G : C(X, ℝ) := ⟨D, hD⟩
  let u : Lp ℝ 2 μ := ContinuousMap.toLp 2 μ ℝ F
  let v : Lp ℝ 2 μ := ContinuousMap.toLp 2 μ ℝ G
  have hUV : inner ℝ u v = ∫ x, R x * D x ∂μ := by
    calc
      inner ℝ u v = ∫ x, G x * conj (F x) ∂μ :=
        MeasureTheory.ContinuousMap.inner_toLp (μ := μ) F G
      _ = ∫ x, R x * D x ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        simp [F, G, mul_comm]
  have hUU : inner ℝ u u = ∫ x, (R x) ^ 2 ∂μ := by
    calc
      inner ℝ u u = ∫ x, F x * conj (F x) ∂μ :=
        MeasureTheory.ContinuousMap.inner_toLp (μ := μ) F F
      _ = ∫ x, (R x) ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        simp [F, pow_two]
  have hVV : inner ℝ v v = ∫ x, (D x) ^ 2 ∂μ := by
    calc
      inner ℝ v v = ∫ x, G x * conj (G x) ∂μ :=
        MeasureTheory.ContinuousMap.inner_toLp (μ := μ) G G
      _ = ∫ x, (D x) ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        simp [G, pow_two]
  have hCS :
      (∫ x, R x * D x ∂μ) ^ 2 ≤
        (∫ x, (R x) ^ 2 ∂μ) * (∫ x, (D x) ^ 2 ∂μ) := by
    have h := real_inner_mul_inner_self_le u v
    rw [hUV, hUU, hVV] at h
    nlinarith [h]
  let Q : ℝ := ∫ x, (D x) ^ 2 ∂μ
  let K : ℝ := ∫ x, R x * D x ∂μ
  let P : ℝ := ∫ x, (R x) ^ 2 ∂μ
  have hQpos : 0 < Q := hQ
  have hK : (K / Q) * Q = K := by
    exact div_mul_cancel₀ K hQpos.ne'
  have hProd : (Q * (K / Q) ^ 2) * Q ≤ P * Q := by
    calc
      (Q * (K / Q) ^ 2) * Q = ((K / Q) * Q) ^ 2 := by ring
      _ = K ^ 2 := by rw [hK]
      _ ≤ P * Q := hCS
  change Q * (K / Q) ^ 2 ≤ P
  exact (mul_le_mul_right₀ hQpos.ne').mp hProd

/-- Difference of two ORIGINAL normalized Wilson posterior densities
with left physical endpoints identity and the genuine pi-rotation at e.
The right endpoint is the original physical background configuration. -/
noncomputable def p4Q2GB_originalWilsonPosteriorLeftDensityContrast
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
    H 2 (by norm_num) beta hbeta
    (originalWilsonExplicitIdentityBoundary H) right e g -
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
    H 2 (by norm_num) beta hbeta
    (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e g

/-- ACTUAL signed physical source response tested against the
nonzero true Wilson posterior density contrast. The denominator is
the true squared HAAR density-row distance of GA, never a made-up
Gram or a new conditional Haar measure. -/
noncomputable def p4Q2GB_originalPhysicalSourcePosteriorContrastProjection
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) : ℝ :=
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)
  let R := p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
    H 2 (by norm_num) beta hbeta f e
  let D := p4Q2GB_originalWilsonPosteriorLeftDensityContrast
    H beta hbeta z.2 e
  (∫ g, R (z,g) * D g ∂μ) /
    p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
      H beta hbeta z.2 e

/-- The first genuinely source-aware bridge: the EXACT ORIGINAL
FG physical-source Wilson conditional RMS is bounded below by its
projection onto the GA density-contrast mode. Any vanishing of
the source projection remains an explicitly visible obstruction. -/
theorem p4Q2GB_originalWilsonConditionalSourceRMS_projection_floor
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    Real.exp (-16 * beta) *
      (Real.exp (-32 * beta) *
        (beta ^ 2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance) *
        (p4Q2GB_originalPhysicalSourcePosteriorContrastProjection
          H beta (le_of_lt hbeta) f e z) ^ 2) ≤
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
  let a := p4Q2GB_originalPhysicalSourcePosteriorContrastProjection
    H beta (le_of_lt hbeta) f e z
  let c := Real.exp (-32 * beta) *
    (beta ^ 2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance)
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
  have hFloor : c ≤ Q :=
    p4Q2GA_originalSU2WilsonPosteriorLeftSensitivityHaarSq_uniform_lower
      H beta (le_of_lt hbeta) z.2 e
  have hcPos : 0 < c :=
    mul_pos (Real.exp_pos _)
      (mul_pos (pow_pos hbeta 2)
        p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance_pos)
  have hQPos : 0 < Q := lt_of_lt_of_le hcPos hFloor
  have hProjection : Q * a ^ 2 ≤ ∫ g, (R g) ^ 2 ∂μ := by
    convert p4Q2GB_continuousProbability_projection_sq_le
      μ R D hR hD (by change 0 < Q; exact hQPos) using 1
  have hHaarLower :
      Real.exp (-16 * beta) *
        (p4Q2FM_originalWilsonRelativeSignedHaarSquaredMoment
          H 2 (by norm_num) beta (le_of_lt hbeta) f e z) ≤
      p4Q2FG_originalWilsonRelativeResponseConditionalSquare
        H 2 (by norm_num) beta (le_of_lt hbeta) f e z :=
    (p4Q2FM_originalWilsonConditionalRMS_real_haar_sandwich
      H 2 (by norm_num) beta (le_of_lt hbeta) f e z).1
  change Real.exp (-16 * beta) * (c * a ^ 2) ≤
    p4Q2FG_originalWilsonRelativeResponseConditionalSquare
      H 2 (by norm_num) beta (le_of_lt hbeta) f e z
  calc
    Real.exp (-16 * beta) * (c * a ^ 2) ≤
        Real.exp (-16 * beta) * (Q * a ^ 2) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hFloor (sq_nonneg a))
        (Real.exp_pos _).le
    _ ≤ Real.exp (-16 * beta) * (∫ g, (R g) ^ 2 ∂μ) :=
      mul_le_mul_of_nonneg_left hProjection (Real.exp_pos _).le
    _ = Real.exp (-16 * beta) *
        p4Q2FM_originalWilsonRelativeSignedHaarSquaredMoment
          H 2 (by norm_num) beta (le_of_lt hbeta) f e z := rfl
    _ ≤ _ := hHaarLower

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GB_continuousProbability_projection_sq_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GB_originalWilsonConditionalSourceRMS_projection_floor
