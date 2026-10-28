import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPosteriorEffectiveLinkParticipationV5_PZ37AAO
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimarySpatialPlaquetteTranslationOrbit
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AAP — true spatial translation orbits and Wilson posterior obstruction

On the ORIGINAL even-periodic finite spatial Wilson lattice, every actual
spatial link is a pair (time-zero source vertex, positive spatial direction).
We construct exact bijective zero-time spatial translations of those links,
prove compatibility with the existing four-dimensional physical edge
translation, and prove that translation orbits are TRANSITIVE on each of
the three ORIGINAL positive spatial directions.

This provides an exact (not assumed) geometric reduction of the true
two-interacting-Wilson-posterior response problem: the remaining
physical condition is translation covariance of AAK's original
full-pair-Haar integrated link response J_(H,b,e). We prove that
this condition is equivalent to J being constant for links within
each direction. We DO NOT assert the condition itself without a proof
of covariance of both interacting Wilson posteriors, their variance,
the boundary pair-Haar measure and the exact centered physical source.

If that explicitly identified TRUE-posterior translation covariance
holds, then the original source-normalized j_(H,b,e) obeys

    j_e <= 3 * R_(H,b) / |Links_H|,
    M2_(H,b) <= 3 * R_(H,b)^2,
    P_(H,b) >= 1/3,

and at least one twelfth of the ORIGINAL spatial links have response
j_e >= R_(H,b)/(2*|Links_H|). These are conditional, mathematically
sharp directional-orbit bounds; they are independent of volume at
frozen H,b but the threshold uses the actual R_(H,b) and can decay.

No source replacement, Haar-posterior surrogate, artificial links,
new axioms/sorry/admit/native_decide, volume-uniform coercivity,
common positive-fine interval, E/F, H1-H4 or continuum mass gap.
This file is append-only. Existing original theorem carriers remain
unchanged.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37AAP_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AAP_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AAP_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AAP_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AAP_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

private noncomputable instance p4Q2PZ37AAP_vertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

section SpatialTranslation
variable (H : ℕ)

local notation "V" => PeriodicHypercubicEvenSpatialSliceVertex H
local notation "D" => PeriodicHypercubicEvenSpatialDirection
local notation "E" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Disp" => PeriodicHypercubicEvenSpatialDisplacement H

/-- Spatial displacements are genuine periodic 4D vertices with
zero Euclidean-time coordinate. Addition and subtraction preserve
the ORIGINAL primary time-zero slice. -/
def p4Q2PZ37AAP_actualSpatialVertexTranslation
    (a : Disp) : V ≃ V where
  toFun v := ⟨v.1 + a.1, by
    change (v.1 + a.1) 0 = 0
    have hv : v.1 0 = 0 := v.2
    simp [hv, a.2]⟩
  invFun v := ⟨v.1 - a.1, by
    change (v.1 - a.1) 0 = 0
    have hv : v.1 0 = 0 := v.2
    simp [hv, a.2]⟩
  left_inv v := by
    apply Subtype.ext
    change (v.1 + a.1) - a.1 = v.1
    abel
  right_inv v := by
    apply Subtype.ext
    change (v.1 - a.1) + a.1 = v.1
    abel

/-- Translation on *all* original time-zero spatial links is bijective;
the positive spatial direction is unchanged. -/
def p4Q2PZ37AAP_actualSpatialLinkTranslation
    (a : Disp) : E ≃ E where
  toFun e := (p4Q2PZ37AAP_actualSpatialVertexTranslation H a e.1, e.2)
  invFun e := ((p4Q2PZ37AAP_actualSpatialVertexTranslation H a).symm e.1, e.2)
  left_inv e := by
    apply Prod.ext
    · exact (p4Q2PZ37AAP_actualSpatialVertexTranslation H a).left_inv e.1
    · rfl
  right_inv e := by
    apply Prod.ext
    · exact (p4Q2PZ37AAP_actualSpatialVertexTranslation H a).right_inv e.1
    · rfl

/-- A genuine spatial-slice link translation commutes exactly with
the existing physical 4D positive-edge embedding and edge translation. -/
theorem p4Q2PZ37AAP_spatialLinkEmbedding_translation
    (a : Disp) (e : E) :
    periodicHypercubicEvenSpatialSliceLinkEmbedding H
        (p4Q2PZ37AAP_actualSpatialLinkTranslation H a e) =
      periodicHypercubicEdgeTranslationEquiv
        (PeriodicHypercubicEvenSideLength H) a.1
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H e) := by
  rfl

/-- Spatial translations act transitively on the entire TRUE
positive-link fiber over any one of the three original directions.
No Wilson posterior or source is involved in this geometry theorem. -/
theorem p4Q2PZ37AAP_spatialTranslation_transitive_sameDirection
    (e f : E) (hdir : e.2 = f.2) :
    ∃ a : Disp,
      p4Q2PZ37AAP_actualSpatialLinkTranslation H a e = f := by
  let a : Disp := ⟨f.1.1 - e.1.1, by
    have he : e.1.1 0 = 0 := e.1.2
    have hf : f.1.1 0 = 0 := f.1.2
    simp [he, hf]⟩
  refine ⟨a, ?_⟩
  apply Prod.ext
  · apply Subtype.ext
    change e.1.1 + (f.1.1 - e.1.1) = f.1.1
    abel
  · exact hdir

/-- The genuine AAK original integrated two-interacting-posterior
link response is covariant under every actual zero-time translation.
This is a PROPOSITION about the unchanged model, not an asserted
Wilson-measure invariance theorem. -/
def p4Q2PZ37AAP_originalPosteriorSpatialTranslationCovariant
    (b : ℝ) (hb : 0 < b) : Prop :=
  ∀ (a : Disp) (e : E),
    p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse H b hb
        (p4Q2PZ37AAP_actualSpatialLinkTranslation H a e) =
      p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse H b hb e

/-- Exact obstruction: covariance of ACTUAL integrated Wilson
posterior link responses under true spatial translations is
EQUIVALENT to direction-fiber constancy of these same responses.
The geometric direction-orbit transitivity is proved above.
No unproved covariance proposition is silently discharged. -/
theorem p4Q2PZ37AAP_originalPosteriorTranslation_iff_directionHomogeneous
    (b : ℝ) (hb : 0 < b) :
    p4Q2PZ37AAP_originalPosteriorSpatialTranslationCovariant H b hb ↔
    ∀ e f : E, e.2 = f.2 →
      p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse H b hb e =
        p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse H b hb f := by
  constructor
  · intro h e f hdir
    obtain ⟨a, ha⟩ :=
      p4Q2PZ37AAP_spatialTranslation_transitive_sameDirection H e f hdir
    calc
      p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse H b hb e =
          p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse H b hb
            (p4Q2PZ37AAP_actualSpatialLinkTranslation H a e) := (h a e).symm
      _ = p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse H b hb f := by
        rw [ha]
  · intro h a e
    exact h (p4Q2PZ37AAP_actualSpatialLinkTranslation H a e) e rfl

/-- Normalization by AAJ's SAME original strictly positive Haar
covariance preserves equality of the authentic raw posterior
responses within every spatial direction. The posterior measure
itself is never replaced by Haar. -/
theorem p4Q2PZ37AAP_originalNormalizedLink_directionHomogeneous
    (b : ℝ) (hb : 0 < b)
    (hCov : p4Q2PZ37AAP_originalPosteriorSpatialTranslationCovariant H b hb) :
    ∀ e f : E, e.2 = f.2 →
      p4Q2PZ37AAK_originalNormalizedLinkResponse H b hb e =
        p4Q2PZ37AAK_originalNormalizedLinkResponse H b hb f := by
  have hRaw :=
    (p4Q2PZ37AAP_originalPosteriorTranslation_iff_directionHomogeneous
      H b hb).mp hCov
  intro e f hdir
  exact congrArg
    (fun x : ℝ => (4 * x) / p4Q2PZ37AAJ_originalHaarPlaquetteCovariance H)
    (hRaw e f hdir)

/-- The true 4D lattice has precisely THREE positive spatial link
directions, independent of finite volume. -/
theorem p4Q2PZ37AAP_originalSpatialDirection_card_three :
    Fintype.card D = 3 := by
  decide

/-- The original Wilson posterior has no additional spatial
concentration beyond the three direction orbits IF its actual
full-pair-Haar integrated link response is spatially translation
covariant. In particular the per-link cap is O(R/|Links|), not
AAM's O(1) absolute cap. The hypothesis is a genuine remaining
physical posterior transport obligation. -/
theorem p4Q2PZ37AAP_covariance_implies_originalRelativeLinkCap
    (b : ℝ) (hb : 0 < b)
    (hCov : p4Q2PZ37AAP_originalPosteriorSpatialTranslationCovariant H b hb) :
    ∀ e : E,
      p4Q2PZ37AAK_originalNormalizedLinkResponse H b hb e ≤
        (3 * p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb) /
          (Fintype.card E : ℝ) := by
  classical
  let j : E → ℝ := p4Q2PZ37AAK_originalNormalizedLinkResponse H b hb
  let R : ℝ := p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb
  let m : ℝ := (Fintype.card V : ℝ)
  let k : ℝ := (Fintype.card D : ℝ)
  let L : ℝ := (Fintype.card E : ℝ)
  let v0 : V := (pz37zaSpatialPlaquetteCoordinateFamily H 0).1
  have hm : 0 < m := by
    have h : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v0⟩
    change (0 : ℝ) < (Fintype.card V : ℝ)
    exact_mod_cast h
  have hk3 : k = 3 := by
    change (Fintype.card D : ℝ) = 3
    norm_num [p4Q2PZ37AAP_originalSpatialDirection_card_three]
  have hk : 0 ≤ k := by rw [hk3]; norm_num
  have hL : 0 < L := p4Q2PZ37AAK_originalLinkCount_pos H
  have hUniv :
      (Finset.univ : Finset E) =
        (Finset.univ : Finset V).product (Finset.univ : Finset D) := by
    ext e
    simp
  have hCard : L = m * k := by
    have hNat : Fintype.card E = Fintype.card V * Fintype.card D := by
      calc
        Fintype.card E = (Finset.univ : Finset E).card := by simp
        _ = ((Finset.univ : Finset V).product (Finset.univ : Finset D)).card := by
          rw [hUniv]
        _ = (Finset.univ : Finset V).card *
              (Finset.univ : Finset D).card := by
          rw [Finset.card_product]
        _ = Fintype.card V * Fintype.card D := by simp
    change (Fintype.card E : ℝ) =
      (Fintype.card V : ℝ) * (Fintype.card D : ℝ)
    exact_mod_cast hNat
  have hConst : ∀ e f : E, e.2 = f.2 → j e = j f :=
    p4Q2PZ37AAP_originalNormalizedLink_directionHomogeneous H b hb hCov
  have hR : R = m * (∑ d : D, j (v0,d)) := by
    calc
      R = ∑ e : E, j e :=
        (p4Q2PZ37AAK_originalNormalizedLinkResponse_sum_eq_Rayleigh H b hb).symm
      _ = ∑ v : V, ∑ d : D, j (v,d) := by
        change (Finset.univ : Finset E).sum j =
          (Finset.univ : Finset V).sum
            (fun v => (Finset.univ : Finset D).sum (fun d => j (v,d)))
        rw [hUniv, Finset.sum_product]
      _ = ∑ _v : V, ∑ d : D, j (v0,d) := by
        apply Finset.sum_congr rfl
        intro v _hv
        apply Finset.sum_congr rfl
        intro d _hd
        exact hConst (v,d) (v0,d) rfl
      _ = m * ∑ d : D, j (v0,d) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rfl
  have hOne (d : D) : j (v0,d) ≤ ∑ q : D, j (v0,q) := by
    have hSubset := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ ({d} : Finset D))
      (fun q _hq _hnot =>
        p4Q2PZ37AAK_originalNormalizedLinkResponse_nonneg H b hb (v0,q))
    simpa only [Finset.sum_singleton] using hSubset
  intro e
  have hBound : j e ≤ ∑ d : D, j (v0,d) :=
    (hConst e (v0,e.2) rfl).le.trans (hOne e.2)
  change j e ≤ (3 * R) / L
  apply (le_div_iff₀ hL).mpr
  calc
    j e * L = (j e * m) * k := by rw [hCard]; ring
    _ ≤ ((∑ d : D, j (v0,d)) * m) * k :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hBound hm.le) hk
    _ = 3 * R := by
      rw [hR, hk3]
      ring

/-- Under exact original Wilson posterior translation covariance, the
true finite-volume posterior concentration second moment has the
volume-independent relative upper bound M2 <= 3 R^2. -/
theorem p4Q2PZ37AAP_covariance_implies_originalSecondMomentBound
    (b : ℝ) (hb : 0 < b)
    (hCov : p4Q2PZ37AAP_originalPosteriorSpatialTranslationCovariant H b hb) :
    p4Q2PZ37AAN_originalPosteriorLinkSecondMoment H b hb ≤
      3 * (p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb)^2 := by
  exact p4Q2PZ37AAO_originalRelativeLinkCap_controlsSecondMoment
    H b hb 3
    (p4Q2PZ37AAP_covariance_implies_originalRelativeLinkCap H b hb hCov)

/-- Under TRUE posterior translation covariance, the original Wilson
effective participation fraction is at least one THIRD, independent
of H. The symmetry hypothesis remains an explicit obstruction. -/
theorem p4Q2PZ37AAP_covariance_implies_originalParticipation_third
    (b : ℝ) (hb : 0 < b)
    (hCov : p4Q2PZ37AAP_originalPosteriorSpatialTranslationCovariant H b hb) :
    (1 / 3 : ℝ) ≤
      p4Q2PZ37AAO_originalPosteriorParticipationFraction H b hb := by
  exact p4Q2PZ37AAO_relativeLinkCap_forcesParticipation
    H b hb 3 (by norm_num)
    (p4Q2PZ37AAP_covariance_implies_originalRelativeLinkCap H b hb hCov)

/-- Conditional finite-volume TRUE Wilson link density: at least
1/12 of all ORIGINAL links respond above half of the physical
Rayleigh-average threshold. The condition is transport of genuine
interacting posterior measures, NOT a Haar replacement. -/
theorem p4Q2PZ37AAP_covariance_implies_halfRayleighActiveDensity
    (b : ℝ) (hb : 0 < b)
    (hCov : p4Q2PZ37AAP_originalPosteriorSpatialTranslationCovariant H b hb) :
    ((1 / 12 : ℝ) *
      (Fintype.card E : ℝ)) ≤
        ((p4Q2PZ37AAL_originalActiveLinks H b hb
          ((1 / 2 : ℝ) *
            p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb)).card : ℝ) := by
  have hOneThird :=
    p4Q2PZ37AAP_covariance_implies_originalParticipation_third H b hb hCov
  have hDensity :=
    p4Q2PZ37AAO_originalRelativeActiveLinkDensity
      H b hb (1 / 2 : ℝ) (by norm_num) (by norm_num)
  have hL : (0 : ℝ) ≤ (Fintype.card E : ℝ) := Nat.cast_nonneg _
  have hFactor :
      (1 / 12 : ℝ) ≤
        (1 - (1 / 2 : ℝ))^2 *
          p4Q2PZ37AAO_originalPosteriorParticipationFraction H b hb := by
    nlinarith only [hOneThird]
  exact (mul_le_mul_of_nonneg_right hFactor hL).trans hDensity

end SpatialTranslation
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAP_spatialLinkEmbedding_translation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAP_spatialTranslation_transitive_sameDirection
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAP_originalPosteriorTranslation_iff_directionHomogeneous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAP_originalNormalizedLink_directionHomogeneous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAP_originalSpatialDirection_card_three
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAP_covariance_implies_originalRelativeLinkCap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAP_covariance_implies_originalSecondMomentBound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAP_covariance_implies_originalParticipation_third
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAP_covariance_implies_halfRayleighActiveDensity
