import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalLocalHaarCovariancePosteriorGramCriterionV5_PZ37AAJ
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AAK — actual centered Wilson posterior response per spatial link

AAJ has identified the genuine Gauss-law centered source norm with 1/4 of
the ORIGINAL finite-local four-link-overlap Haar covariance C_H > 0.
Here we DO NOT replace either interacting Wilson posterior by Haar.
Instead we inspect GL's ORIGINAL per-link, complete-boundary-pair-Haar
normalized squared expectation-gap integrals on that SAME centered source.

Each actual spatial link e carries a nonnegative true posterior response
  J_(H,b,e) = integral_pairHaar (gap_(e,z)(V_H)^2 / variance_(e,z)).
The exact original centered GL Gram is SUM_e J_(H,b,e), with no missing
links, finite-context detectors, sampling, or global action surrogate.
Normalizing each response by the *original local* Haar covariance,
  j_(H,b,e) = 4 J_(H,b,e) / C_H,
gives an exact decomposition
  R_(H,b)(V_H) = SUM_e j_(H,b,e).

We kernel-check a true centered two-mode GI detector identity, positivity
of each local response, a strictly positive response on at least one
original link at EVERY fixed finite H and b>0, and the finite average
pigeonhole bound. For ALL volumes a lower bound j_e >= c/|Links_H|
at EVERY genuine link is SUFFICIENT for R >= c; conversely R >= c
REQUIRES at least ONE true link with j_e >= c/|Links_H|.
These are NOT equivalent linkwise hypotheses. In particular one positive
link is not a uniform mass-gap proof. No all-volume positive c, common
positive fine interval, E/F, H1--H4 or continuum gap is asserted.

Append-only, no source/posterior modification, no new axiom, sorry,
admit or native_decide.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37AAK_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AAK_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AAK_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AAK_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AAK_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37AAK_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The literal positive integer number of ORIGINAL spatial links,
not a synthetic lattice-size parameter. -/
theorem p4Q2PZ37AAK_originalLinkCount_pos (H : ℕ) :
    (0 : ℝ) <
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) := by
  classical
  let p := pz37zaSpatialPlaquetteCoordinateFamily H 0
  have hN : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) :=
    Fintype.card_pos_iff.mpr ⟨(p.1, p.2.1.1)⟩
  exact_mod_cast hN

/-- The original pair-Haar Wilson two-posterior GI detector on
the actual centered Gauss-law tangent is a literal mean-subtracted
Wilson source, not an independently chosen compensated direction. -/
theorem p4Q2PZ37AAK_originalCenteredGI_eq_halfMeanSubtractedWilson
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z =
      (1 / 2 : ℝ) *
        (p4Q2JH_originalGIResponseCLM H b hb.le e z
          (ContinuousMap.toLp 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) ℝ
            (p4Q2JI_actualSpatialWilsonContinuous H)) -
        (inner ℝ (p4Q2JU_originalSpatialWilsonPhysicalSource H)
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)) *
          p4Q2JH_originalGIResponseCLM H b hb.le e z
            (ContinuousMap.toLp 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) ℝ
              (1 : C(PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2, ℝ)))) := by
  rw [p4Q2PZ37ZW_originalCenteredDirection_eq_static]
  rw [p4Q2PZ37ZN_originalStaticPhysicalGI_eq_twoModeRow]
  simp [p4Q2PZ37ZW_originalCenteredCoefficients]
  ring

/-- One ACTUAL spatial link's original two-interacting-posterior
squared GI expectation gap divided by the original posterior variance,
integrated over the whole true boundary pair-Haar measure. -/
noncomputable def p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  p4Q2GL_originalWilsonSignedExpectationGapSquareDivVarianceLinkMean
    H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e

/-- Linkwise squared expectation-gap/variance is nonnegative under the
original two positive Wilson posterior density-contrast variance. -/
theorem p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse_nonneg
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 ≤ p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse H b hb e := by
  unfold p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse
    p4Q2GL_originalWilsonSignedExpectationGapSquareDivVarianceLinkMean
  apply integral_nonneg
  intro z
  exact div_nonneg (sq_nonneg _)
    (p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq_pos H b hb z.2 e).le

/-- NO spatial link is omitted: exact finite sum of authentic integrated
posterior response contributions is the genuine ZP/ZX original GL Gram. -/
theorem p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse_sum_eq_gram
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse H b hb e) =
        p4Q2PZ37ZX_originalCenteredGLGramValue H b hb := by
  rw [p4Q2PZ37ZX_originalCenteredGram_eq_originalGLMass]
  rfl

/-- The genuinely model-dependent ORIGINAL centered posterior GL
mass is strictly positive for every finite H and frozen b>0. -/
theorem p4Q2PZ37AAK_originalCenteredLinkResponseSum_pos
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    0 < ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse H b hb e := by
  rw [p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse_sum_eq_gram]
  rw [← p4Q2PZ37AAH_originalExactCenteredRayleighFloor_mul_norm_sq_eq_gram]
  exact mul_pos
    (p4Q2PZ37AAH_originalExactCenteredRayleighFloor_pos H b hb)
    (pow_pos (norm_pos_iff.mpr
      (p4Q2PZ37ZW_originalCenteredDirection_ne_zero H)) 2)

/-- Each true posterior link response measured RELATIVE to the original
strictly positive finite-local product-Haar Wilson covariance.
This is only a numerical normalization, NOT a measure replacement. -/
noncomputable def p4Q2PZ37AAK_originalNormalizedLinkResponse
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  (4 * p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse H b hb e) /
    p4Q2PZ37AAJ_originalHaarPlaquetteCovariance H

/-- Every true local posterior response remains nonnegative after
normalization by the original positive Haar covariance. -/
theorem p4Q2PZ37AAK_originalNormalizedLinkResponse_nonneg
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 ≤ p4Q2PZ37AAK_originalNormalizedLinkResponse H b hb e := by
  unfold p4Q2PZ37AAK_originalNormalizedLinkResponse
  exact div_nonneg
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
      (p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse_nonneg H b hb e))
    (p4Q2PZ37AAJ_originalHaarCovariance_pos H).le

/-- Exact original source-normalized centered physical GL Rayleigh
decomposition as a sum over ALL true spatial links, each with its
own TWO-interacting-Wilson-posterior full pair-Haar response.
In particular no part of the numerator is replaced by reference Haar. -/
theorem p4Q2PZ37AAK_originalNormalizedLinkResponse_sum_eq_Rayleigh
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      p4Q2PZ37AAK_originalNormalizedLinkResponse H b hb e) =
        p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb := by
  let C : ℝ := p4Q2PZ37AAJ_originalHaarPlaquetteCovariance H
  let G : ℝ := p4Q2PZ37ZX_originalCenteredGLGramValue H b hb
  have hC : 0 < C := p4Q2PZ37AAJ_originalHaarCovariance_pos H
  have hC0 : C ≠ 0 := ne_of_gt hC
  have hRayleigh :
      p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb =
        (4 / C) * G := by
    unfold p4Q2PZ37AAH_originalExactCenteredRayleighFloor
    rw [p4Q2PZ37ZX_originalCenteredRayleigh_eq_originalGram_div_physicalNorm,
      p4Q2PZ37AAJ_originalPhysicalNorm_sq_eq_quarterHaarCovariance]
    change G / ((1 / 4 : ℝ) * C) = (4 / C) * G
    field_simp [hC0]
  rw [hRayleigh]
  change (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
    (4 * p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse H b hb e) / C) =
      (4 / C) * G
  calc
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      (4 * p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse H b hb e) / C) =
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        (4 / C) * p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse H b hb e := by
          apply Finset.sum_congr rfl
          intro e _he
          ring
    _ = (4 / C) * (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse H b hb e) := by
      rw [Finset.mul_sum]
    _ = (4 / C) * G := by
      rw [p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse_sum_eq_gram]

/-- The exact real number of actual links is positive and its
constant average sums to its numerator, with no artificial count. -/
private theorem p4Q2PZ37AAK_originalLink_constantAverage_sum
    (H : ℕ) (c : ℝ) :
    (∑ _e : PeriodicHypercubicEvenSpatialSliceLink H,
      c / (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)) = c := by
  let L : ℝ := (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)
  have hL : L ≠ 0 := ne_of_gt
    (p4Q2PZ37AAK_originalLinkCount_pos H)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change L * (c / L) = c
  rw [mul_comm]
  exact div_mul_cancel₀ c hL

/-- At ANY fixed finite H,b there is a genuine original spatial link
whose posterior contrast response is strictly positive. The witness
is a posterior-integrated detector, NOT a pointwise substitute. -/
theorem p4Q2PZ37AAK_exists_originalLink_positiveResponse
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    ∃ e : PeriodicHypercubicEvenSpatialSliceLink H,
      0 < p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse H b hb e := by
  classical
  by_contra h
  push Not at h
  have hSum :
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse H b hb e) ≤ 0 := by
    calc
      _ ≤ ∑ _e : PeriodicHypercubicEvenSpatialSliceLink H, (0 : ℝ) := by
        apply Finset.sum_le_sum
        intro e _he
        exact h e
      _ = 0 := by simp
  exact (not_le_of_gt
    (p4Q2PZ37AAK_originalCenteredLinkResponseSum_pos H b hb)) hSum

/-- A source-normalized fine-zero Rayleigh floor c NECESSARILY has
at least one original spatial link whose actual posterior-integrated
normalized response is at least c/|Links_H|. This is a pigeonhole
obstruction, not an unconditional uniform c. -/
theorem p4Q2PZ37AAK_exists_link_ge_average_of_Rayleigh_floor
    (H : ℕ) (b : ℝ) (hb : 0 < b) (c : ℝ)
    (hFloor : c ≤ p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb) :
    ∃ e : PeriodicHypercubicEvenSpatialSliceLink H,
      c / (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) ≤
        p4Q2PZ37AAK_originalNormalizedLinkResponse H b hb e := by
  classical
  by_contra h
  push Not at h
  let p := pz37zaSpatialPlaquetteCoordinateFamily H 0
  let e0 : PeriodicHypercubicEvenSpatialSliceLink H := (p.1, p.2.1.1)
  have hStrict :
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        p4Q2PZ37AAK_originalNormalizedLinkResponse H b hb e) <
      (∑ _e : PeriodicHypercubicEvenSpatialSliceLink H,
        c / (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)) := by
    apply Finset.sum_lt_sum
    · intro e _he
      exact (h e).le
    · exact ⟨e0, Finset.mem_univ _, h e0⟩
  rw [p4Q2PZ37AAK_originalNormalizedLinkResponse_sum_eq_Rayleigh,
    p4Q2PZ37AAK_originalLink_constantAverage_sum] at hStrict
  exact (not_lt_of_ge hFloor) hStrict

/-- A genuine LINKWISE lower bound on the ORIGINAL normalized two-
posterior integrated response is sufficient for a uniform physical
fine-zero Rayleigh floor. A lower bound at ALL links is strictly
stronger than the necessary single-link witness above. -/
theorem p4Q2PZ37AAK_uniformRayleigh_of_allLink_averageFloor
    (b : ℕ → ℝ) (hb : ∀ H, 0 < b H) (c : ℝ)
    (hLocal : ∀ (H : ℕ) (e : PeriodicHypercubicEvenSpatialSliceLink H),
      c / (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) ≤
        p4Q2PZ37AAK_originalNormalizedLinkResponse H (b H) (hb H) e) :
    ∀ H : ℕ,
      c ≤ p4Q2PZ37AAH_originalExactCenteredRayleighFloor H (b H) (hb H) := by
  classical
  intro H
  have hSum :
      (∑ _e : PeriodicHypercubicEvenSpatialSliceLink H,
        c / (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)) ≤
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        p4Q2PZ37AAK_originalNormalizedLinkResponse H (b H) (hb H) e) := by
    apply Finset.sum_le_sum
    intro e _he
    exact hLocal H e
  rw [p4Q2PZ37AAK_originalLink_constantAverage_sum,
    p4Q2PZ37AAK_originalNormalizedLinkResponse_sum_eq_Rayleigh] at hSum
  exact hSum

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAK_originalLinkCount_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAK_originalCenteredGI_eq_halfMeanSubtractedWilson
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse_sum_eq_gram
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAK_originalCenteredLinkResponseSum_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAK_originalNormalizedLinkResponse_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAK_originalNormalizedLinkResponse_sum_eq_Rayleigh
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAK_exists_originalLink_positiveResponse
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAK_exists_link_ge_average_of_Rayleigh_floor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAK_uniformRayleigh_of_allLink_averageFloor
