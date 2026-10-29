import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalUnweightedGIGapAutomaticIntegrabilityV5_PZ37AAZ2
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ABA — independent ORIGINAL Wilson FX cap from FK

This append-only file closes ONE of AAZ2's two genuine analytic gates:
an upper bound on the original normalized SU(2) Wilson two-posterior
Haar-L² contrast Q. The proof uses the TRUE FK interacting one-link
density sandwich directly, without importing JL's legacy theorem.
In particular it imports no finite-incidence native_decide certificate.

For every finite H, original right background and actual link,
  Q_(H,b,e) <= (exp(16*b) - exp(-16*b))^2
at b >= 0. For 0 < b(H) <= B, the same genuine Q has the
volume-independent cap q_B = (exp(16*B)-exp(-16*B))^2 > 0.

The AAZ2 original unweighted GI moment criterion is consequently
strengthened: a UNIFORM positive m on the UNCHANGED original centered
physical two-interacting-Wilson-posterior expectation-gap squared
moment, plus a genuine upper coupling B, now implies the fine-zero
physical Rayleigh floor m/(18*q_B) WITHOUT an assumed FX cap.

The volume-uniform GI moment m is NOT established here; it is a separate
unresolved noncancellation / cylinder localization task. No change
to source, Wilson kernel, two posterior laws, outer pair-Haar, or
Gauss-law Hilbert space; no new axioms, sorry/admit/native_decide,
conditional-posterior surrogate, common fine interval, E/F, H1-H4,
or continuum Yang-Mills mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37ABA_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ABA_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ABA_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ABA_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ABA_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ABA_haarProbability :
    IsProbabilityMeasure (normalizedCompactHaar G) :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint

/-- Direct original-FK bound on the contrast of TWO ACTUAL normalized
interacting Wilson conditional posterior densities, with no JL lemma. -/
theorem p4Q2PZ37ABA_originalPosteriorContrast_abs_le_from_FK
    (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) (g : G) :
    |p4Q2GB_originalWilsonPosteriorLeftDensityContrast H b hb right e g| ≤
      Real.exp (16 * b) - Real.exp (-16 * b) := by
  have h0 := p4Q2FK_originalWilsonPosteriorConditionalDensity_twoSided
    H 2 (by norm_num) b hb
    (originalWilsonExplicitIdentityBoundary H) right e g
  have h1 := p4Q2FK_originalWilsonPosteriorConditionalDensity_twoSided
    H 2 (by norm_num) b hb
    (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e g
  unfold p4Q2GB_originalWilsonPosteriorLeftDensityContrast
  apply abs_le.mpr
  constructor
  · linarith [h0.1, h1.2]
  · linarith [h0.2, h1.1]

/-- Actual original FX contrast Haar-L² squared is capped
uniformly over all H, true links and right configurations.
Only the original FK density theorem supplies the envelope. -/
theorem p4Q2PZ37ABA_originalFXVariance_le_FK_envelope
    (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
      H b hb right e ≤
      (Real.exp (16 * b) - Real.exp (-16 * b)) ^ 2 := by
  let μ : Measure G := normalizedCompactHaar G
  let c : ℝ := Real.exp (16 * b) - Real.exp (-16 * b)
  let P0 : G → ℝ := fun g =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
      H 2 (by norm_num) b hb
      (originalWilsonExplicitIdentityBoundary H) right e g
  let P1 : G → ℝ := fun g =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
      H 2 (by norm_num) b hb
      (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e g
  let D : G → ℝ := fun g =>
    p4Q2GB_originalWilsonPosteriorLeftDensityContrast H b hb right e g
  have hP0 : Continuous P0 := by
    change Continuous (continuousNormalizedExp μ
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
        H 2 (by norm_num) b hb
        (originalWilsonExplicitIdentityBoundary H) right e))
    exact continuous_continuousNormalizedExp μ _
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
        H 2 (by norm_num) b hb
        (originalWilsonExplicitIdentityBoundary H) right e)
  have hP1 : Continuous P1 := by
    change Continuous (continuousNormalizedExp μ
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
        H 2 (by norm_num) b hb
        (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e))
    exact continuous_continuousNormalizedExp μ _
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
        H 2 (by norm_num) b hb
        (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e)
  have hD : Continuous D := by
    change Continuous (fun g => P0 g - P1 g)
    exact hP0.sub hP1
  have hDsq : Integrable (fun g => (D g) ^ 2) μ :=
    (hD.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hc : 0 ≤ c := by
    exact le_trans (abs_nonneg _)
      (p4Q2PZ37ABA_originalPosteriorContrast_abs_le_from_FK
        H b hb right e (1 : G))
  have hBound (g : G) : (D g) ^ 2 ≤ c ^ 2 := by
    have ha :=
      p4Q2PZ37ABA_originalPosteriorContrast_abs_le_from_FK
        H b hb right e g
    change |D g| ≤ c at ha
    have hlo := (abs_le.mp ha).1
    have hhi := (abs_le.mp ha).2
    have hp : 0 ≤ (c - D g) * (c + D g) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  change (∫ g : G, (D g) ^ 2 ∂μ) ≤ c ^ 2
  calc
    (∫ g : G, (D g) ^ 2 ∂μ) ≤
        ∫ _g : G, c ^ 2 ∂μ := by
      apply integral_mono hDsq (integrable_const _)
      intro g
      exact hBound g
    _ = c ^ 2 := by simp

/-- The genuine original FX upper cap is uniform in H once the
unchanged positive Wilson coupling is bounded from above by B. -/
theorem p4Q2PZ37ABA_originalFXVariance_le_commonCap
    (H : ℕ) (b B : ℝ) (hb : 0 ≤ b) (hbB : b ≤ B)
    (right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
      H b hb right e ≤
      (Real.exp (16 * B) - Real.exp (-16 * B)) ^ 2 := by
  let c : ℝ := Real.exp (16 * b) - Real.exp (-16 * b)
  let C : ℝ := Real.exp (16 * B) - Real.exp (-16 * B)
  have hTop : 16 * b ≤ 16 * B := by linarith
  have hBottom : -16 * B ≤ -16 * b := by linarith
  have hExpTop : Real.exp (16 * b) ≤ Real.exp (16 * B) :=
    Real.exp_le_exp.mpr hTop
  have hExpBottom : Real.exp (-16 * B) ≤ Real.exp (-16 * b) :=
    Real.exp_le_exp.mpr hBottom
  have hc : 0 ≤ c := by
    exact le_trans (abs_nonneg _)
      (p4Q2PZ37ABA_originalPosteriorContrast_abs_le_from_FK
        H b hb right e (1 : G))
  have hC : 0 ≤ C := by
    dsimp [C, c] at *
    linarith
  have hcc : c ≤ C := by
    dsimp [c, C]
    linarith
  have hSquare : c ^ 2 ≤ C ^ 2 := by
    have hProduct : 0 ≤ (C - c) * (C + c) :=
      mul_nonneg (sub_nonneg.mpr hcc) (add_nonneg hC hc)
    nlinarith
  exact (p4Q2PZ37ABA_originalFXVariance_le_FK_envelope
    H b hb right e).trans hSquare

/-- Explicit strictly positive common FX cap when B>0. -/
theorem p4Q2PZ37ABA_commonFXCap_pos
    (B : ℝ) (hB : 0 < B) :
    0 < (Real.exp (16 * B) - Real.exp (-16 * B)) ^ 2 := by
  have h : -16 * B < 16 * B := by linarith
  have hExp : Real.exp (-16 * B) < Real.exp (16 * B) :=
    Real.exp_lt_exp.mpr h
  exact pow_pos (sub_pos.mpr hExp) 2

/-- One genuinely UNSOLVED microscopic input remains: the uniform
unweighted GI-gap moment m>0. The FX upper bound is now a PROVED
original-Wilson consequence of FK and bounded original couplings. -/
theorem p4Q2PZ37ABA_allVolumes_Rayleigh_of_unweightedGIMoments_boundedCoupling
    (b : ℕ → ℝ) (hb : ∀ H, 0 < b H)
    (B : ℝ) (hBound : ∀ H, b H ≤ B)
    (m : ℝ) (hm : 0 < m)
    (e : ∀ H, PeriodicHypercubicEvenSpatialSliceLink H)
    (hMoment : ∀ H,
      m ≤ p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment
        H (b H) (hb H) (e H)) :
    0 < (m / ((Real.exp (16 * B) - Real.exp (-16 * B)) ^ 2)) / 18 ∧
      ∀ H,
        (m / ((Real.exp (16 * B) - Real.exp (-16 * B)) ^ 2)) / 18 ≤
          p4Q2PZ37AAH_originalExactCenteredRayleighFloor H (b H) (hb H) := by
  have hB : 0 < B := (hb 0).trans_le (hBound 0)
  have hq : 0 < (Real.exp (16 * B) - Real.exp (-16 * B)) ^ 2 :=
    p4Q2PZ37ABA_commonFXCap_pos B hB
  apply p4Q2PZ37AAZ2_allVolumes_Rayleigh_of_unweightedGIMoments
    b hb m ((Real.exp (16 * B) - Real.exp (-16 * B)) ^ 2)
    hm hq e
  · intro H z
    exact p4Q2PZ37ABA_originalFXVariance_le_commonCap
      H (b H) B (hb H).le (hBound H) z.2 (e H)
  · exact hMoment

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABA_originalPosteriorContrast_abs_le_from_FK
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABA_originalFXVariance_le_FK_envelope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABA_originalFXVariance_le_commonCap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABA_commonFXCap_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABA_allVolumes_Rayleigh_of_unweightedGIMoments_boundedCoupling
