import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalLinkPosteriorResponseLocalizationV5_PZ37AAK
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AAL — genuine retained-link density and posterior response

PZ37AAK represents the exact normalized physical centered Wilson
Rayleigh R_(H,b)(V_H) as a sum of nonnegative contributions j_(H,b,e)
over all ACTUAL finite spatial links. No gauge, source, or posterior
is changed. An arbitrary FINITE subset S of those same links retains
a genuine partial original posterior response; this is NOT a
substitute for the full-link GL mass.

This file proves that partial response is nonnegative, monotone in S
and bounded above by the full genuine Rayleigh. More importantly,
a retained set of actual link density at least delta with each
normalized response at least alpha / |Links_H| yields

    R_(H,b)(V_H) >= delta * alpha.

Equivalently, a genuine raw two-interacting-Wilson-posterior
integrated response bound J_e >= kappa*C_H/|Links_H| on such a set
implies R >= 4*delta*kappa, where C_H>0 is the ORIGINAL centered
product-Haar covariance established in AAJ. Haar is used ONLY for
normalizing the physical source, never as an interacting posterior.

A genuinely defined ACTUAL active-link set at a response threshold
makes the density premise testable, not hypothetical new links.
At each fixed H and frozen b>0, an active set exists with a positive
volume-dependent threshold. A uniform positive density and response
threshold remain UNSOLVED; there is no all-volume coercivity claim,
no common fine interval, endpoint E/F, H1-H4 or continuum mass gap.

Append-only, tighten-only, same authoritative theorem carrier.
No new axiom, sorry, admit or native_decide.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37AAL_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AAL_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AAL_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AAL_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AAL_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37AAL_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The actual original normalized posterior response RESTRICTED to
a finite subset of genuine spatial links. It is just a partial sum
of AAK's original nonnegative link contributions. -/
noncomputable def p4Q2PZ37AAL_originalRetainedLinkRayleigh
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) : ℝ :=
  ∑ e ∈ S, p4Q2PZ37AAK_originalNormalizedLinkResponse H b hb e

theorem p4Q2PZ37AAL_originalRetainedLinkRayleigh_nonneg
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) :
    0 ≤ p4Q2PZ37AAL_originalRetainedLinkRayleigh H b hb S := by
  unfold p4Q2PZ37AAL_originalRetainedLinkRayleigh
  exact Finset.sum_nonneg (fun e _he =>
    p4Q2PZ37AAK_originalNormalizedLinkResponse_nonneg H b hb e)

/-- Retaining MORE authentic original links cannot reduce the original
posterior response, since EACH genuine link integral is nonnegative. -/
theorem p4Q2PZ37AAL_originalRetainedLinkRayleigh_mono
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    {S T : Finset (PeriodicHypercubicEvenSpatialSliceLink H)}
    (hST : S ⊆ T) :
    p4Q2PZ37AAL_originalRetainedLinkRayleigh H b hb S ≤
      p4Q2PZ37AAL_originalRetainedLinkRayleigh H b hb T := by
  unfold p4Q2PZ37AAL_originalRetainedLinkRayleigh
  exact Finset.sum_le_sum_of_subset_of_nonneg hST
    (fun e _he _hnot =>
      p4Q2PZ37AAK_originalNormalizedLinkResponse_nonneg H b hb e)

/-- The retained sum never exceeds the TRUE original full-link
source-normalized posterior Rayleigh. No truncation is promoted to
the authority of the full physical numerator. -/
theorem p4Q2PZ37AAL_originalRetainedLinkRayleigh_le_originalRayleigh
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) :
    p4Q2PZ37AAL_originalRetainedLinkRayleigh H b hb S ≤
      p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb := by
  rw [← p4Q2PZ37AAK_originalNormalizedLinkResponse_sum_eq_Rayleigh]
  exact p4Q2PZ37AAL_originalRetainedLinkRayleigh_mono
    H b hb (Finset.subset_univ S)

/-- Elementary exact count normalization, not a Wilson-model
assumption. The denominator is the ACTUAL positive link count. -/
private theorem p4Q2PZ37AAL_count_density_mul_le
    (L n delta alpha : ℝ)
    (hL : 0 < L) (ha : 0 ≤ alpha)
    (hDensity : delta * L ≤ n) :
    delta * alpha ≤ n * (alpha / L) := by
  have hDiv : 0 ≤ alpha / L := div_nonneg ha hL.le
  have hMul := mul_le_mul_of_nonneg_right hDensity hDiv
  have hEq : (delta * L) * (alpha / L) = delta * alpha := by
    field_simp [ne_of_gt hL]
  calc
    delta * alpha = (delta * L) * (alpha / L) := hEq.symm
    _ ≤ n * (alpha / L) := hMul

/-- A positive DENSITY of truly retained links, each with an original
posterior response at least alpha/|Links_H|, suffices for a finite-H
physical Rayleigh floor delta*alpha. The OTHER links are merely
nonnegative; no global all-link lower bound is postulated. -/
theorem p4Q2PZ37AAL_originalRetainedDensity_response_lower
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H))
    (delta alpha : ℝ) (ha : 0 ≤ alpha)
    (hDensity :
      delta * (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) ≤
        (S.card : ℝ))
    (hStrong : ∀ e ∈ S,
      alpha / (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) ≤
        p4Q2PZ37AAK_originalNormalizedLinkResponse H b hb e) :
    delta * alpha ≤
      p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb := by
  classical
  let L : ℝ := (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)
  have hL : 0 < L := p4Q2PZ37AAK_originalLinkCount_pos H
  have hCard : delta * alpha ≤
      (S.card : ℝ) * (alpha / L) :=
    p4Q2PZ37AAL_count_density_mul_le L (S.card : ℝ)
      delta alpha hL ha hDensity
  have hConstant :
      (∑ _e ∈ S, alpha / L) = (S.card : ℝ) * (alpha / L) := by
    simp only [Finset.sum_const, nsmul_eq_mul]
  have hPartial :
      (∑ _e ∈ S, alpha / L) ≤
        p4Q2PZ37AAL_originalRetainedLinkRayleigh H b hb S := by
    unfold p4Q2PZ37AAL_originalRetainedLinkRayleigh
    exact Finset.sum_le_sum (fun e he => hStrong e he)
  calc
    delta * alpha ≤ (S.card : ℝ) * (alpha / L) := hCard
    _ = ∑ _e ∈ S, alpha / L := hConstant.symm
    _ ≤ p4Q2PZ37AAL_originalRetainedLinkRayleigh H b hb S := hPartial
    _ ≤ p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb :=
      p4Q2PZ37AAL_originalRetainedLinkRayleigh_le_originalRayleigh H b hb S

/-- Same density estimate expressed DIRECTLY in genuine original raw
two-interacting-posterior J_e and strictly positive original product-
Haar centered covariance C_H. No reference-Haar posterior surrogate. -/
theorem p4Q2PZ37AAL_originalRawPosteriorResponse_density_lower
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H))
    (delta kappa : ℝ) (hk : 0 ≤ kappa)
    (hDensity :
      delta * (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) ≤
        (S.card : ℝ))
    (hRaw : ∀ e ∈ S,
      (kappa * p4Q2PZ37AAJ_originalHaarPlaquetteCovariance H) /
        (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) ≤
        p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse H b hb e) :
    delta * (4 * kappa) ≤
      p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb := by
  let L : ℝ := (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)
  let C : ℝ := p4Q2PZ37AAJ_originalHaarPlaquetteCovariance H
  have hL : 0 < L := p4Q2PZ37AAK_originalLinkCount_pos H
  have hC : 0 < C := p4Q2PZ37AAJ_originalHaarCovariance_pos H
  apply p4Q2PZ37AAL_originalRetainedDensity_response_lower
    H b hb S delta (4 * kappa) (by positivity) hDensity
  intro e he
  change (4 * kappa) / L ≤
    (4 * p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse H b hb e) / C
  have hRaw' : kappa * C ≤
      p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse H b hb e * L :=
    (div_le_iff₀ hL).mp (hRaw e he)
  exact (div_le_div_iff₀ hL hC).mpr (by nlinarith)

/-- Full-volume family: positive DENSITY plus positive STRENGTH on
some actual retained subset S_H gives a common positive fine-ZERO
centered physical Rayleigh lower bound. Both premises are explicitly
volume-uniform assumptions, NOT conclusions of finite-H positivity. -/
theorem p4Q2PZ37AAL_uniformFineZero_of_retainedDensityStrength
    (b : ℕ → ℝ) (hb : ∀ H, 0 < b H)
    (S : ∀ H : ℕ, Finset (PeriodicHypercubicEvenSpatialSliceLink H))
    (delta alpha : ℝ) (hd : 0 < delta) (ha : 0 < alpha)
    (hDensity : ∀ H : ℕ,
      delta * (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) ≤
        ((S H).card : ℝ))
    (hStrong : ∀ (H : ℕ) (e : PeriodicHypercubicEvenSpatialSliceLink H),
      e ∈ S H →
      alpha / (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) ≤
        p4Q2PZ37AAK_originalNormalizedLinkResponse H (b H) (hb H) e) :
    0 < delta * alpha ∧ ∀ H : ℕ,
      delta * alpha ≤
        p4Q2PZ37AAH_originalExactCenteredRayleighFloor H (b H) (hb H) := by
  refine ⟨mul_pos hd ha, ?_⟩
  intro H
  exact p4Q2PZ37AAL_originalRetainedDensity_response_lower
    H (b H) (hb H) (S H) delta alpha ha.le
    (hDensity H) (fun e he => hStrong H e he)

/-- ACTUAL active original Wilson links at response threshold
alpha/|Links_H|. Each index is one of the original spatial links;
nothing in the physical model or interacting posterior is changed. -/
noncomputable def p4Q2PZ37AAL_originalActiveLinks
    (H : ℕ) (b : ℝ) (hb : 0 < b) (alpha : ℝ) :
    Finset (PeriodicHypercubicEvenSpatialSliceLink H) := by
  classical
  exact Finset.univ.filter (fun e =>
    alpha / (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) ≤
      p4Q2PZ37AAK_originalNormalizedLinkResponse H b hb e)

theorem p4Q2PZ37AAL_mem_originalActiveLinks_iff
    (H : ℕ) (b : ℝ) (hb : 0 < b) (alpha : ℝ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    e ∈ p4Q2PZ37AAL_originalActiveLinks H b hb alpha ↔
      alpha / (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) ≤
        p4Q2PZ37AAK_originalNormalizedLinkResponse H b hb e := by
  classical
  simp [p4Q2PZ37AAL_originalActiveLinks]

/-- The ACTUAL positive-threshold active set is nonempty whenever
the original centered physical Rayleigh exceeds that threshold.
This is AAK's exact one-link NECESSARY witness. -/
theorem p4Q2PZ37AAL_originalActiveLinks_nonempty_of_Rayleigh_floor
    (H : ℕ) (b : ℝ) (hb : 0 < b) (alpha : ℝ)
    (hFloor : alpha ≤ p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb) :
    (p4Q2PZ37AAL_originalActiveLinks H b hb alpha).Nonempty := by
  obtain ⟨e, he⟩ :=
    p4Q2PZ37AAK_exists_link_ge_average_of_Rayleigh_floor
      H b hb alpha hFloor
  exact ⟨e, (p4Q2PZ37AAL_mem_originalActiveLinks_iff H b hb alpha e).mpr he⟩

/-- At EACH original finite H,b>0, the actual active-link set has
some strictly positive but possibly volume-dependent threshold. This
proves no common positive threshold or density across H. -/
theorem p4Q2PZ37AAL_exists_positive_originalActiveThreshold
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    ∃ alpha : ℝ, 0 < alpha ∧
      (p4Q2PZ37AAL_originalActiveLinks H b hb alpha).Nonempty := by
  let alpha : ℝ := p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb
  refine ⟨alpha, p4Q2PZ37AAH_originalExactCenteredRayleighFloor_pos H b hb, ?_⟩
  exact p4Q2PZ37AAL_originalActiveLinks_nonempty_of_Rayleigh_floor
    H b hb alpha (le_refl alpha)

/-- Concrete true active subset version: to obtain an all-volume
positive fine-ZERO Rayleigh floor, it suffices that a FIXED fraction
of ORIGINAL links exceed the FIXED genuine normalized posterior
response threshold. These uniform density assumptions are UNPROVED. -/
theorem p4Q2PZ37AAL_uniformFineZero_of_activeLinkDensity
    (b : ℕ → ℝ) (hb : ∀ H, 0 < b H)
    (delta alpha : ℝ) (hd : 0 < delta) (ha : 0 < alpha)
    (hActiveDensity : ∀ H : ℕ,
      delta * (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) ≤
        (p4Q2PZ37AAL_originalActiveLinks H (b H) (hb H) alpha).card) :
    ∀ H : ℕ, 0 < delta * alpha ∧
      delta * alpha ≤
        p4Q2PZ37AAH_originalExactCenteredRayleighFloor H (b H) (hb H) := by
  intro H
  refine ⟨mul_pos hd ha, ?_⟩
  exact p4Q2PZ37AAL_originalRetainedDensity_response_lower
    H (b H) (hb H)
    (p4Q2PZ37AAL_originalActiveLinks H (b H) (hb H) alpha)
    delta alpha ha.le (hActiveDensity H)
    (fun e he =>
      (p4Q2PZ37AAL_mem_originalActiveLinks_iff H (b H) (hb H) alpha e).mp he)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAL_originalRetainedLinkRayleigh_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAL_originalRetainedLinkRayleigh_mono
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAL_originalRetainedLinkRayleigh_le_originalRayleigh
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAL_originalRetainedDensity_response_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAL_originalRawPosteriorResponse_density_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAL_uniformFineZero_of_retainedDensityStrength
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAL_mem_originalActiveLinks_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAL_originalActiveLinks_nonempty_of_Rayleigh_floor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAL_exists_positive_originalActiveThreshold
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAL_uniformFineZero_of_activeLinkDensity
