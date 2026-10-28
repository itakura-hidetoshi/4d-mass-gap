import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalLinkPosteriorCapConcentrationV5_PZ37AAM
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AAN — original Wilson posterior link second moment and concentration

AAK's actual source-normalized centered Wilson physical Rayleigh is exactly
the sum of the ORIGINAL two-interacting-Wilson-posterior link responses
  R_(H,b)(V_H) = ∑_e j_(H,b,e),   j_(H,b,e) ≥ 0.
AAM's pointwise upper cap is O(1), not O(1/|Links_H|).

This file constructs the *actual*, dimensionless, volume-normalized
second moment of the SAME original posterior response:
  M2_(H,b) := |Links_H| * ∑_e j_(H,b,e)^2.

Finite Cauchy--Schwarz gives R^2 ≤ M2 without a new hypothesis. More
importantly, if R ≥ c and the true active set
  S_(H,b,alpha) = {e : j_e ≥ alpha / |Links_H|}
has cardinality s, then the genuine posterior obeys the concentration
tradeoff
  (c-alpha)^2 * |Links_H| ≤ s * M2_(H,b)
for 0 ≤ alpha ≤ c.

Consequently, a *separately established* all-volume upper bound M2≤K,
together with R≥c>0, would force a positive fraction of ACTUAL active
links, with alpha=c/2 and density at least c²/(4K). Conversely sparse
active links and a positive Rayleigh floor force a large M2.

The existing AAM link cap yields only
  M2 ≤ |Links_H| * (2/exp(-16b)) * R,
which cannot by itself provide K independent of H. All new definitions
refer to authentic original link/posterior integrals, not surrogate
sources or Haar replacements. No uniform M2 estimate, uniform
coercivity, shared positive fine interval, endpoints E/F, H1--H4,
or continuum mass gap is claimed. Append-only, no new axioms,
sorry, admit, native_decide, or changes to previous theorem carriers.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37AAN_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AAN_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AAN_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AAN_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AAN_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37AAN_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Dimensionless second moment of the ACTUAL, original Wilson
two-interacting-posterior link response, normalized by the actual link
count. No reference posterior or test-vector substitution occurs. -/
noncomputable def p4Q2PZ37AAN_originalPosteriorLinkSecondMoment
    (H : ℕ) (b : ℝ) (hb : 0 < b) : ℝ :=
  (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
    ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      (p4Q2PZ37AAK_originalNormalizedLinkResponse H b hb e)^2

theorem p4Q2PZ37AAN_originalPosteriorSecondMoment_nonneg
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    0 ≤ p4Q2PZ37AAN_originalPosteriorLinkSecondMoment H b hb := by
  unfold p4Q2PZ37AAN_originalPosteriorLinkSecondMoment
  exact mul_nonneg (Nat.cast_nonneg _)
    (Finset.sum_nonneg (fun e _he => sq_nonneg _))

/-- Exact (finite) Cauchy--Schwarz on the genuine original Wilson
posterior link contributions: the second moment dominates R². -/
theorem p4Q2PZ37AAN_originalRayleigh_sq_le_posteriorSecondMoment
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    (p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb)^2 ≤
      p4Q2PZ37AAN_originalPosteriorLinkSecondMoment H b hb := by
  have hCS := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)))
    (f := fun e => p4Q2PZ37AAK_originalNormalizedLinkResponse H b hb e)
  simpa only [Finset.card_univ,
    p4Q2PZ37AAK_originalNormalizedLinkResponse_sum_eq_Rayleigh,
    p4Q2PZ37AAN_originalPosteriorLinkSecondMoment] using hCS

/-- The exact localization/concentration obstruction for ACTUAL
two-posterior Wilson link responses. A Rayleigh floor c cannot be
carried by too few threshold-active original links unless the actual
normalized second moment is large. No moment bound is assumed. -/
theorem p4Q2PZ37AAN_originalActiveCount_secondMoment_tradeoff
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (c alpha : ℝ) (hAlpha : 0 ≤ alpha) (hAlphaLe : alpha ≤ c)
    (hFloor : c ≤ p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb) :
    (c - alpha)^2 *
        (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) ≤
      ((p4Q2PZ37AAL_originalActiveLinks H b hb alpha).card : ℝ) *
        p4Q2PZ37AAN_originalPosteriorLinkSecondMoment H b hb := by
  classical
  let j : PeriodicHypercubicEvenSpatialSliceLink H → ℝ :=
    p4Q2PZ37AAK_originalNormalizedLinkResponse H b hb
  let S : Finset (PeriodicHypercubicEvenSpatialSliceLink H) :=
    p4Q2PZ37AAL_originalActiveLinks H b hb alpha
  let L : ℝ := (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)
  have hL : 0 < L := p4Q2PZ37AAK_originalLinkCount_pos H
  have hInactive (e : PeriodicHypercubicEvenSpatialSliceLink H)
      (he : e ∈ (Finset.univ \ S)) : j e ≤ alpha / L := by
    have hnot : e ∉ S := (Finset.mem_sdiff.mp he).2
    have hNotLarge : ¬ alpha / L ≤ j e := by
      intro hlarge
      exact hnot ((p4Q2PZ37AAL_mem_originalActiveLinks_iff
        H b hb alpha e).mpr hlarge)
    exact le_of_lt (lt_of_not_ge hNotLarge)
  have hTcard : (((Finset.univ \ S).card : ℝ)) ≤ L := by
    have hNat : (Finset.univ \ S).card ≤
        Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) := by
      simpa only [Finset.card_univ] using
        (Finset.card_le_card (Finset.sdiff_subset :
          (Finset.univ \ S) ⊆ (Finset.univ :
            Finset (PeriodicHypercubicEvenSpatialSliceLink H))))
    exact_mod_cast hNat
  have hInactiveSum : (∑ e ∈ Finset.univ \ S, j e) ≤ alpha := by
    calc
      (∑ e ∈ Finset.univ \ S, j e) ≤
          ∑ _e ∈ Finset.univ \ S, alpha / L :=
        Finset.sum_le_sum (fun e he => hInactive e he)
      _ = ((Finset.univ \ S).card : ℝ) * (alpha / L) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ L * (alpha / L) :=
        mul_le_mul_of_nonneg_right hTcard (div_nonneg hAlpha hL.le)
      _ = alpha := by field_simp [ne_of_gt hL]
  have hDecomp :
      (∑ e ∈ Finset.univ \ S, j e) + (∑ e ∈ S, j e) =
        p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb := by
    calc
      _ = ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, j e := by
        simpa using (Finset.sum_sdiff
          (s₁ := S)
          (s₂ := (Finset.univ :
            Finset (PeriodicHypercubicEvenSpatialSliceLink H)))
          (f := j) (Finset.subset_univ S))
      _ = p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb := by
        exact p4Q2PZ37AAK_originalNormalizedLinkResponse_sum_eq_Rayleigh H b hb
  have hActive : c - alpha ≤ ∑ e ∈ S, j e := by
    linarith only [hFloor, hInactiveSum, hDecomp]
  have hCS :
      (∑ e ∈ S, j e)^2 ≤
        (S.card : ℝ) * ∑ e ∈ S, (j e)^2 := by
    simpa only using (sq_sum_le_card_mul_sum_sq (s := S) (f := j))
  have hSubsetSq :
      (∑ e ∈ S, (j e)^2) ≤
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, (j e)^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun e _he _hnot => sq_nonneg (j e))
  have hCard : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
  have hSq :
      (c - alpha)^2 ≤
        (S.card : ℝ) *
          ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, (j e)^2 :=
    (pow_le_pow_left₀ (sub_nonneg.mpr hAlphaLe) hActive 2).trans
      (hCS.trans (mul_le_mul_of_nonneg_left hSubsetSq hCard))
  have hMul := mul_le_mul_of_nonneg_right hSq hL.le
  change (c - alpha)^2 * L ≤
    (S.card : ℝ) *
      (L * ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, (j e)^2)
  calc
    (c - alpha)^2 * L ≤
        ((S.card : ℝ) *
          ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, (j e)^2) * L := hMul
    _ = (S.card : ℝ) *
          (L * ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, (j e)^2) := by ring

/-- A *conditional* uniform bound on the actual second moment converts
the Rayleigh floor to a quantitative density of ACTUAL Wilson links.
This is strictly sharper than AAM's order-one pointwise bound. -/
theorem p4Q2PZ37AAN_originalActiveDensity_of_posteriorSecondMomentBound
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (c alpha K : ℝ) (hAlpha : 0 ≤ alpha) (hAlphaLe : alpha ≤ c)
    (hK : 0 < K)
    (hFloor : c ≤ p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb)
    (hMoment : p4Q2PZ37AAN_originalPosteriorLinkSecondMoment H b hb ≤ K) :
    ((c - alpha)^2 / K) *
        (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) ≤
      ((p4Q2PZ37AAL_originalActiveLinks H b hb alpha).card : ℝ) := by
  have hTrade := p4Q2PZ37AAN_originalActiveCount_secondMoment_tradeoff
    H b hb c alpha hAlpha hAlphaLe hFloor
  have hKTrade :
      (c - alpha)^2 *
          (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) ≤
        ((p4Q2PZ37AAL_originalActiveLinks H b hb alpha).card : ℝ) * K :=
    hTrade.trans (mul_le_mul_of_nonneg_left hMoment (Nat.cast_nonneg _))
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ hK).mpr (by nlinarith only [hKTrade])

/-- Uniform second-moment nonconcentration plus a pre-existing
all-volume positive Rayleigh floor would force positive original
posterior active-link density, at threshold c/(2|Links_H|).
Neither uniform premise is asserted here. -/
theorem p4Q2PZ37AAN_uniformActiveDensity_of_uniformPosteriorSecondMoment
    (b : ℕ → ℝ) (hb : ∀ H, 0 < b H)
    (c K : ℝ) (hc : 0 < c) (hK : 0 < K)
    (hFloor : ∀ H : ℕ,
      c ≤ p4Q2PZ37AAH_originalExactCenteredRayleighFloor H (b H) (hb H))
    (hMoment : ∀ H : ℕ,
      p4Q2PZ37AAN_originalPosteriorLinkSecondMoment H (b H) (hb H) ≤ K) :
    ∀ H : ℕ,
      (((c / 2)^2 / K) *
        (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)) ≤
          ((p4Q2PZ37AAL_originalActiveLinks H (b H) (hb H)
            (c / 2)).card : ℝ) := by
  intro H
  have h := p4Q2PZ37AAN_originalActiveDensity_of_posteriorSecondMomentBound
    H (b H) (hb H) c (c / 2) K
    (by positivity) (by linarith) hK (hFloor H) (hMoment H)
  have hHalf : c - c / 2 = c / 2 := by ring
  simpa only [hHalf] using h

/-- A fixed Rayleigh floor and sparse ACTUAL active links force the
genuine posterior second moment to be large. This is a quantified
localization obstruction, not an assertion that the links are sparse. -/
theorem p4Q2PZ37AAN_sparseActiveLinks_force_posteriorSecondMoment
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (c alpha delta : ℝ) (hAlpha : 0 ≤ alpha)
    (hAlphaLe : alpha ≤ c) (hDelta : 0 < delta)
    (hFloor : c ≤ p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb)
    (hSparse :
      ((p4Q2PZ37AAL_originalActiveLinks H b hb alpha).card : ℝ) ≤
        delta * (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)) :
    (c - alpha)^2 / delta ≤
      p4Q2PZ37AAN_originalPosteriorLinkSecondMoment H b hb := by
  let L : ℝ := (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)
  have hL : 0 < L := p4Q2PZ37AAK_originalLinkCount_pos H
  have hMomentNonneg := p4Q2PZ37AAN_originalPosteriorSecondMoment_nonneg H b hb
  have hTrade := p4Q2PZ37AAN_originalActiveCount_secondMoment_tradeoff
    H b hb c alpha hAlpha hAlphaLe hFloor
  have hSparseMul :=
    mul_le_mul_of_nonneg_right hSparse hMomentNonneg
  have hBasic : (c - alpha)^2 ≤
      delta * p4Q2PZ37AAN_originalPosteriorLinkSecondMoment H b hb := by
    apply (mul_le_mul_right hL).mp
    nlinarith only [hTrade, hSparseMul]
  exact (div_le_iff₀ hDelta).mpr hBasic

/-- The ACTUAL AAM pointwise Wilson posterior cap bounds M2 only by
|Links_H| times the true physical Rayleigh. Thus it is NOT a uniform
M2 certificate in the all-volume problem. -/
theorem p4Q2PZ37AAN_actualPosteriorCap_secondMoment_volumeCost
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    p4Q2PZ37AAN_originalPosteriorLinkSecondMoment H b hb ≤
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
        ((2 / Real.exp (-16 * b)) *
          p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb) := by
  let j : PeriodicHypercubicEvenSpatialSliceLink H → ℝ :=
    p4Q2PZ37AAK_originalNormalizedLinkResponse H b hb
  let L : ℝ := (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)
  let cap : ℝ := 2 / Real.exp (-16 * b)
  have hL : 0 ≤ L := (p4Q2PZ37AAK_originalLinkCount_pos H).le
  have hLocal (e : PeriodicHypercubicEvenSpatialSliceLink H) :
      (j e)^2 ≤ cap * j e := by
    have h0 := p4Q2PZ37AAK_originalNormalizedLinkResponse_nonneg H b hb e
    have hcap :=
      p4Q2PZ37AAM_originalNormalizedLinkResponse_le_explicitPosteriorCap H b hb e
    have hProduct : 0 ≤ j e * (cap - j e) :=
      mul_nonneg h0 (sub_nonneg.mpr hcap)
    nlinarith only [hProduct]
  have hSum :
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, (j e)^2) ≤
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, cap * j e :=
    Finset.sum_le_sum (fun e _he => hLocal e)
  change L * (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, (j e)^2) ≤
    L * (cap * p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb)
  calc
    L * (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, (j e)^2) ≤
        L * (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, cap * j e) :=
      mul_le_mul_of_nonneg_left hSum hL
    _ = L * (cap * ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, j e) := by
      rw [← Finset.mul_sum]
    _ = L * (cap * p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb) := by
      rw [p4Q2PZ37AAK_originalNormalizedLinkResponse_sum_eq_Rayleigh]

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAN_originalPosteriorSecondMoment_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAN_originalRayleigh_sq_le_posteriorSecondMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAN_originalActiveCount_secondMoment_tradeoff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAN_originalActiveDensity_of_posteriorSecondMomentBound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAN_uniformActiveDensity_of_uniformPosteriorSecondMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAN_sparseActiveLinks_force_posteriorSecondMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAN_actualPosteriorCap_secondMoment_volumeCost
