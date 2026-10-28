import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPosteriorLinkSecondMomentConcentrationV5_PZ37AAN
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AAO — original Wilson posterior effective-link participation

AAN kernel-checked the exact TRUE two-interacting-Wilson-posterior
link second moment M2_(H,b) = |Links_H| * sum_e j_(H,b,e)^2
and the concentration tradeoff. AAK proved the genuine physical
Rayleigh R_(H,b) = sum_e j_(H,b,e) > 0, with j_(H,b,e) >= 0.

Define the exact, dimensionless original posterior participation fraction

    P_(H,b) := R_(H,b)^2 / M2_(H,b).

This file establishes UNCONDITIONALLY at each original finite volume:

    0 < 1/|Links_H| <= P_(H,b) <= 1,

and for each theta in [0,1] the genuine threshold-active link set

    S_(theta) := {original e : j_(H,b,e) >= theta*R_(H,b)/|Links_H|}

obeys the deterministic posterior Paley--Zygmund inequality

    |S_(theta)| >= (1-theta)^2 * P_(H,b) * |Links_H|.

This is a REAL quantitative finite-H statement, not an all-volume
lower density theorem. A separate sufficient LOCAL anti-concentration
hypothesis j_e <= kappa*R/|Links_H| gives M2 <= kappa*R^2,
P >= 1/kappa, and a corresponding positive fraction of truly active
links. No such volume-uniform local posterior hypothesis is asserted.

In particular positivity of each finite-H participation fraction
does NOT imply a common positive lower bound over H; the rigorous
unconditional floor 1/|Links_H| may decay to zero.

Every j, R, M2 and active set is the actual original Wilson posterior
object from AAK/AAL/AAN. No interacting posterior or physical source
is replaced by product Haar or by a surrogate detector. No new axiom,
sorry/admit/native_decide, coercivity, shared positive-fine interval,
E/F, H1--H4, or continuum Yang--Mills mass gap is claimed.
Append-only theorem carrier, no alteration to earlier declarations.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37AAO_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AAO_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AAO_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AAO_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AAO_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37AAO_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Exact TRUE original Wilson posterior effective participation
fraction, normalized to the complete original link set. -/
noncomputable def p4Q2PZ37AAO_originalPosteriorParticipationFraction
    (H : ℕ) (b : ℝ) (hb : 0 < b) : ℝ :=
  (p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb)^2 /
    p4Q2PZ37AAN_originalPosteriorLinkSecondMoment H b hb

/-- Finite-H positivity of the original posterior second moment:
the physical centered Wilson Rayleigh is strictly positive and its
square is bounded above by the genuine second moment (AAN). -/
theorem p4Q2PZ37AAO_originalPosteriorSecondMoment_pos
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    0 < p4Q2PZ37AAN_originalPosteriorLinkSecondMoment H b hb := by
  have hR := p4Q2PZ37AAH_originalExactCenteredRayleighFloor_pos H b hb
  have hCS :=
    p4Q2PZ37AAN_originalRayleigh_sq_le_posteriorSecondMoment H b hb
  exact lt_of_lt_of_le (pow_pos hR 2) hCS

/-- Unconditional reverse finite-sum bound M2 <= |Links_H| R^2.
Every true nonnegative link response j_e is at most the full original
Rayleigh, since all other original links contribute nonnegatively. -/
theorem p4Q2PZ37AAO_originalPosteriorSecondMoment_le_card_Rayleigh_sq
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    p4Q2PZ37AAN_originalPosteriorLinkSecondMoment H b hb ≤
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
        (p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb)^2 := by
  classical
  let j : PeriodicHypercubicEvenSpatialSliceLink H → ℝ :=
    p4Q2PZ37AAK_originalNormalizedLinkResponse H b hb
  let R : ℝ := p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb
  let L : ℝ := (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)
  have hL : 0 ≤ L := (p4Q2PZ37AAK_originalLinkCount_pos H).le
  have hLink (e : PeriodicHypercubicEvenSpatialSliceLink H) : j e ≤ R := by
    simpa only [p4Q2PZ37AAL_originalRetainedLinkRayleigh,
      Finset.sum_singleton] using
      (p4Q2PZ37AAL_originalRetainedLinkRayleigh_le_originalRayleigh
        H b hb ({e} : Finset (PeriodicHypercubicEvenSpatialSliceLink H)))
  have hLocal (e : PeriodicHypercubicEvenSpatialSliceLink H) :
      (j e)^2 ≤ R * j e := by
    have hNonneg := p4Q2PZ37AAK_originalNormalizedLinkResponse_nonneg H b hb e
    have hMul := mul_le_mul_of_nonneg_right (hLink e) hNonneg
    nlinarith only [hMul]
  have hSum :
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, (j e)^2) ≤ R^2 := by
    calc
      _ ≤ ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, R * j e :=
        Finset.sum_le_sum (fun e _he => hLocal e)
      _ = R * (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, j e) := by
        rw [← Finset.mul_sum]
      _ = R^2 := by
        rw [p4Q2PZ37AAK_originalNormalizedLinkResponse_sum_eq_Rayleigh]
        ring
  change L * (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, (j e)^2) ≤
    L * R^2
  exact mul_le_mul_of_nonneg_left hSum hL

/-- The physically realized posterior participation is strictly
positive and lies between the inverse ACTUAL link count and one.
Neither bound is uniform in volume without additional information. -/
theorem p4Q2PZ37AAO_originalPosteriorParticipation_bounds
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    0 < p4Q2PZ37AAO_originalPosteriorParticipationFraction H b hb ∧
    1 / (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) ≤
      p4Q2PZ37AAO_originalPosteriorParticipationFraction H b hb ∧
    p4Q2PZ37AAO_originalPosteriorParticipationFraction H b hb ≤ 1 := by
  let R : ℝ := p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb
  let M : ℝ := p4Q2PZ37AAN_originalPosteriorLinkSecondMoment H b hb
  let L : ℝ := (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)
  have hR : 0 < R := p4Q2PZ37AAH_originalExactCenteredRayleighFloor_pos H b hb
  have hM : 0 < M := p4Q2PZ37AAO_originalPosteriorSecondMoment_pos H b hb
  have hL : 0 < L := p4Q2PZ37AAK_originalLinkCount_pos H
  have hLower : R^2 ≤ M :=
    p4Q2PZ37AAN_originalRayleigh_sq_le_posteriorSecondMoment H b hb
  have hUpper : M ≤ L * R^2 :=
    p4Q2PZ37AAO_originalPosteriorSecondMoment_le_card_Rayleigh_sq H b hb
  constructor
  · change 0 < R^2 / M
    exact div_pos (pow_pos hR 2) hM
  constructor
  · change (1 : ℝ) / L ≤ R^2 / M
    exact (div_le_div_iff₀ hL hM).mpr (by nlinarith only [hUpper])
  · change R^2 / M ≤ (1 : ℝ)
    exact (div_le_iff₀ hM).mpr (by simpa only [one_mul] using hLower)

/-- Unconditional exact-Paley--Zygmund lower density of truly active
ORIGINAL spatial links at the ADAPTIVE posterior average threshold.
The threshold uses the actual finite-volume Rayleigh R and therefore
does not by itself give a fixed positive alpha across volumes. -/
theorem p4Q2PZ37AAO_originalRelativeActiveLinkDensity
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (theta : ℝ) (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1) :
    ((1 - theta)^2 *
        p4Q2PZ37AAO_originalPosteriorParticipationFraction H b hb) *
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) ≤
        ((p4Q2PZ37AAL_originalActiveLinks H b hb
          (theta * p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb)).card : ℝ) := by
  let R : ℝ := p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb
  let M : ℝ := p4Q2PZ37AAN_originalPosteriorLinkSecondMoment H b hb
  let L : ℝ := (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)
  let S : Finset (PeriodicHypercubicEvenSpatialSliceLink H) :=
    p4Q2PZ37AAL_originalActiveLinks H b hb (theta * R)
  have hR : 0 < R := p4Q2PZ37AAH_originalExactCenteredRayleighFloor_pos H b hb
  have hM : 0 < M := p4Q2PZ37AAO_originalPosteriorSecondMoment_pos H b hb
  have hAlpha : 0 ≤ theta * R := mul_nonneg htheta0 hR.le
  have hAlphaLe : theta * R ≤ R := by
    simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right htheta1 hR.le)
  have hTrade : (R - theta * R)^2 * L ≤ (S.card : ℝ) * M :=
    p4Q2PZ37AAN_originalActiveCount_secondMoment_tradeoff
      H b hb R (theta * R) hAlpha hAlphaLe (le_refl R)
  have hSquare : (R - theta * R)^2 = (1 - theta)^2 * R^2 := by ring
  rw [hSquare] at hTrade
  change ((1 - theta)^2 * (R^2 / M)) * L ≤ (S.card : ℝ)
  calc
    ((1 - theta)^2 * (R^2 / M)) * L =
        (((1 - theta)^2 * R^2) * L) / M := by ring
    _ ≤ (S.card : ℝ) := (div_le_iff₀ hM).mpr hTrade

/-- A sufficient LOCAL comparison directly on the original posterior:
if every genuine link has normalized response at most kappa times the
actual Rayleigh average, then M2 <= kappa * R^2. This condition is
NOT established by AAM's O(1) per-link cap. -/
theorem p4Q2PZ37AAO_originalRelativeLinkCap_controlsSecondMoment
    (H : ℕ) (b : ℝ) (hb : 0 < b) (kappa : ℝ)
    (hPoint : ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
      p4Q2PZ37AAK_originalNormalizedLinkResponse H b hb e ≤
        (kappa * p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb) /
          (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)) :
    p4Q2PZ37AAN_originalPosteriorLinkSecondMoment H b hb ≤
      kappa * (p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb)^2 := by
  classical
  let j : PeriodicHypercubicEvenSpatialSliceLink H → ℝ :=
    p4Q2PZ37AAK_originalNormalizedLinkResponse H b hb
  let R : ℝ := p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb
  let L : ℝ := (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)
  have hL : 0 < L := p4Q2PZ37AAK_originalLinkCount_pos H
  have hLocal (e : PeriodicHypercubicEvenSpatialSliceLink H) :
      (j e)^2 ≤ ((kappa * R) / L) * j e := by
    have hNonneg := p4Q2PZ37AAK_originalNormalizedLinkResponse_nonneg H b hb e
    have hMul := mul_le_mul_of_nonneg_right (hPoint e) hNonneg
    nlinarith only [hMul]
  have hSum :
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, (j e)^2) ≤
        ((kappa * R) / L) * R := by
    calc
      _ ≤ ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          ((kappa * R) / L) * j e :=
        Finset.sum_le_sum (fun e _he => hLocal e)
      _ = ((kappa * R) / L) *
            (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, j e) := by
        rw [← Finset.mul_sum]
      _ = ((kappa * R) / L) * R := by
        rw [p4Q2PZ37AAK_originalNormalizedLinkResponse_sum_eq_Rayleigh]
  change L * (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, (j e)^2) ≤
    kappa * R^2
  calc
    L * (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, (j e)^2) ≤
        L * (((kappa * R) / L) * R) :=
      mul_le_mul_of_nonneg_left hSum hL.le
    _ = kappa * R^2 := by
      field_simp [ne_of_gt hL] <;> ring

/-- Genuine original per-link *relative* posterior cap kappa forces
participation at least 1/kappa. The premise is a sharply identified
unproved localization input, not an all-volume Wilson conclusion. -/
theorem p4Q2PZ37AAO_relativeLinkCap_forcesParticipation
    (H : ℕ) (b : ℝ) (hb : 0 < b) (kappa : ℝ) (hk : 0 < kappa)
    (hPoint : ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
      p4Q2PZ37AAK_originalNormalizedLinkResponse H b hb e ≤
        (kappa * p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb) /
          (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)) :
    1 / kappa ≤ p4Q2PZ37AAO_originalPosteriorParticipationFraction H b hb := by
  let R : ℝ := p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb
  let M : ℝ := p4Q2PZ37AAN_originalPosteriorLinkSecondMoment H b hb
  have hM : 0 < M := p4Q2PZ37AAO_originalPosteriorSecondMoment_pos H b hb
  have hBound : M ≤ kappa * R^2 :=
    p4Q2PZ37AAO_originalRelativeLinkCap_controlsSecondMoment H b hb kappa hPoint
  change (1 : ℝ) / kappa ≤ R^2 / M
  exact (div_le_div_iff₀ hk hM).mpr (by nlinarith only [hBound])

/-- Pointwise relative posterior anti-concentration implies genuinely
positive ACTIVE ORIGINAL link density, at every fixed H,b. A uniform
kappa would make the density bound volume-independent, although the
threshold here still depends on R_(H,b). -/
theorem p4Q2PZ37AAO_relativeLinkCap_forcesActiveDensity
    (H : ℕ) (b : ℝ) (hb : 0 < b) (kappa theta : ℝ)
    (hk : 0 < kappa) (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (hPoint : ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
      p4Q2PZ37AAK_originalNormalizedLinkResponse H b hb e ≤
        (kappa * p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb) /
          (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)) :
    (((1 - theta)^2 / kappa) *
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)) ≤
        ((p4Q2PZ37AAL_originalActiveLinks H b hb
          (theta * p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb)).card : ℝ) := by
  let L : ℝ := (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)
  have hL : 0 ≤ L := (p4Q2PZ37AAK_originalLinkCount_pos H).le
  have hPart : 1 / kappa ≤
      p4Q2PZ37AAO_originalPosteriorParticipationFraction H b hb :=
    p4Q2PZ37AAO_relativeLinkCap_forcesParticipation H b hb kappa hk hPoint
  have hDensity :=
    p4Q2PZ37AAO_originalRelativeActiveLinkDensity H b hb theta htheta0 htheta1
  calc
    ((1 - theta)^2 / kappa) * L =
        ((1 - theta)^2 * (1 / kappa)) * L := by ring
    _ ≤ ((1 - theta)^2 *
        p4Q2PZ37AAO_originalPosteriorParticipationFraction H b hb) * L :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hPart (sq_nonneg _)) hL
    _ ≤ ((p4Q2PZ37AAL_originalActiveLinks H b hb
          (theta * p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb)).card : ℝ) :=
      hDensity

/-- Uniform relative posterior participation would give positive
DENSITY of links active above one-half the actual Rayleigh average.
No volume-independent Rayleigh floor or participation bound is proved. -/
theorem p4Q2PZ37AAO_uniformHalfRayleighActiveDensity_of_participationFloor
    (b : ℕ → ℝ) (hb : ∀ H, 0 < b H)
    (delta : ℝ) (hdelta : 0 < delta)
    (hParticipation : ∀ H : ℕ,
      delta ≤ p4Q2PZ37AAO_originalPosteriorParticipationFraction
        H (b H) (hb H)) :
    0 < delta / 4 ∧ ∀ H : ℕ,
      (delta / 4) *
        (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) ≤
          ((p4Q2PZ37AAL_originalActiveLinks H (b H) (hb H)
            ((1 / 2 : ℝ) *
              p4Q2PZ37AAH_originalExactCenteredRayleighFloor H (b H) (hb H))).card : ℝ) := by
  constructor
  · positivity
  intro H
  let L : ℝ := (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)
  have hL : 0 ≤ L := (p4Q2PZ37AAK_originalLinkCount_pos H).le
  have hDensity :=
    p4Q2PZ37AAO_originalRelativeActiveLinkDensity
      H (b H) (hb H) (1 / 2 : ℝ) (by norm_num) (by norm_num)
  calc
    (delta / 4) * L =
        ((1 - (1 / 2 : ℝ))^2 * delta) * L := by ring
    _ ≤ ((1 - (1 / 2 : ℝ))^2 *
        p4Q2PZ37AAO_originalPosteriorParticipationFraction H (b H) (hb H)) * L :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hParticipation H) (sq_nonneg _)) hL
    _ ≤ ((p4Q2PZ37AAL_originalActiveLinks H (b H) (hb H)
          ((1 / 2 : ℝ) *
            p4Q2PZ37AAH_originalExactCenteredRayleighFloor H (b H) (hb H))).card : ℝ) :=
      hDensity

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAO_originalPosteriorSecondMoment_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAO_originalPosteriorSecondMoment_le_card_Rayleigh_sq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAO_originalPosteriorParticipation_bounds
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAO_originalRelativeActiveLinkDensity
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAO_originalRelativeLinkCap_controlsSecondMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAO_relativeLinkCap_forcesParticipation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAO_relativeLinkCap_forcesActiveDensity
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAO_uniformHalfRayleighActiveDensity_of_participationFloor
