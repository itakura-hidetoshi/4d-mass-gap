import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalAJAQFreeBudgetObstructionV5_PZ37AJW
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AJX — original AJA certificate's absolute sixteenth budget

The true, unchanged original normalized margin m, Haar negative region R,
centered source f0, normalized Wilson transfer S, and full top Q are used.

Unlike AJV's insufficient q-free upper estimate, this leaf provides an
independent absolute ceiling on the ACTUAL original AJA budget:

  B = m² * Measure.real mu(R) <= V/16,   V=||f0||² > 0.

Indeed AIW gives m<=b*V/2, b=beta*exp(-beta*p);
the genuine Haar probability has mass<=1; AIS gives V<=p²/4;
and beta*p/exp(beta*p)<=1. We do not change the certificate.

For any hypothesized genuine Wilson finite-power witness below B:
  ||S^n f0||² < V/16;
  ||Q f0||² < V/16;
  ||(Q^⊥) f0||² > 15 V/16;
  (inner f0 Omega)^2 < V/16;
  ||extraTop||² < V/16.

The large (>15/16) genuine excited-source energy is NECESSARY, not
an established fact. If the true source's top energy is >=V/16,
the original AJA witness cannot exist. No top simplicity is assumed.
Even an attainable 15/16 excitation criterion alone does not prove
strict AJA smallness. Mass gap/uniform coercivity remain unproved.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- A sharper certificate-only ceiling than AJW's joint eighth bound.
This holds for the *same* finite-H original real-Haar certificate.
No assumption about the actual full-top projection appears. -/
theorem real_margin_probability_budget_le_sixteenth_ajx
    (p V b m mass : ℝ)
    (hp : 0 < p) (hV : 0 ≤ V)
    (hVcap : V ≤ p ^ 2 / 4)
    (hb : 0 ≤ b) (hbp : b * p ≤ 1)
    (hm : 0 ≤ m) (hmub : m ≤ b * V / 2)
    (hmass : mass ≤ 1) :
    m ^ 2 * mass ≤ V / 16 := by
  have hbp0 : 0 ≤ b * p := mul_nonneg hb hp.le
  have hbp2 : (b * p) ^ 2 ≤ (1 : ℝ) := by
    simpa only [one_pow] using
      (sq_le_sq₀ hbp0 (by norm_num)).2 hbp
  have hbp2' : b ^ 2 * p ^ 2 ≤ (1 : ℝ) := by
    nlinarith only [hbp2]
  have hScaled : b ^ 2 * V ≤ b ^ 2 * (p ^ 2 / 4) :=
    mul_le_mul_of_nonneg_left hVcap (sq_nonneg b)
  have hQuarter : b ^ 2 * V ≤ (1 : ℝ) / 4 := by
    nlinarith only [hScaled, hbp2']
  have hPowerBound : (b * V) ^ 2 ≤ V / 4 := by
    have h := mul_le_mul_of_nonneg_right hQuarter hV
    nlinarith only [h]
  have hbHalf : 0 ≤ b * V / 2 := by positivity
  have hmSq : m ^ 2 ≤ (b * V / 2) ^ 2 :=
    (sq_le_sq₀ hm hbHalf).2 hmub
  have hMarginMass : m ^ 2 * mass ≤ m ^ 2 := by
    calc
      m ^ 2 * mass ≤ m ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hmass (sq_nonneg m)
      _ = m ^ 2 := by ring
  nlinarith only [hmSq, hPowerBound, hMarginMass]

local notation "GX" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AJX_group : IsTopologicalGroup GX :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AJX_compact : CompactSpace GX :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AJX_secondCountable : SecondCountableTopology GX :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AJX_measurable : MeasurableSpace GX :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AJX_borel : BorelSpace GX :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AJX_linkFintype (K : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink K) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "PhysX" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "CfgX" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muX" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "VX" =>
  p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "pX" =>
  p4Q2PZ37AFZ_plaquetteCount H
local notation "fX" =>
  p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "SX" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "TopX" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace H 2 (by norm_num)
local notation "OmegaX" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector H 2 (by norm_num)
local notation "uX" =>
  p4Q2PZ37AIW_originalNormalizedSourceTransfer H
local notation "mX" =>
  p4Q2PZ37AIW_originalNormalizedNegativeMargin H

local instance p4Q2PZ37AJX_physicalComplete (K : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule K 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    K 2).completeSpace_coe

local instance p4Q2PZ37AJX_topComplete
    (K : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
        K 2 (by norm_num) beta hbeta) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_isClosed
    K 2 (by norm_num) beta hbeta).completeSpace_coe

/-- An unconditional ORIGINAL AJA upper certificate ceiling: the true
negative-region Haar margin budget occupies at most 1/16 of source variance.
AJA's strictly positive lower *source-image* certificate is unchanged. -/
theorem p4Q2PZ37AJX_originalAJA_certificate_le_sixteenth_variance
    (beta : ℝ) (hbeta : 0 < beta) :
    (mX beta hbeta.le) ^ 2 *
      Measure.real muX
        {B : CfgX | uX beta hbeta.le B < -(mX beta hbeta.le)}
      ≤ VX / 16 := by
  let b : ℝ := beta * Real.exp (-(beta * pX))
  have hp : 0 < pX := p4Q2PZ37AHN_count_pos H
  have hV : 0 < VX :=
    (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hVcap : VX ≤ pX ^ 2 / 4 :=
    p4Q2PZ37AIS_originalSourceSecondMoment_le_countSquare H
  have hb : 0 ≤ b := by
    dsimp [b]
    positivity
  have hbp : b * pX ≤ 1 := by
    have hExp : beta * pX ≤ Real.exp (beta * pX) := by
      linarith only [Real.add_one_le_exp (beta * pX)]
    have hDiv : beta * pX / Real.exp (beta * pX) ≤ 1 :=
      (div_le_iff₀ (Real.exp_pos _)).2 (by linarith only [hExp])
    calc
      b * pX = beta * pX / Real.exp (beta * pX) := by
        dsimp [b]
        rw [Real.exp_neg]
        ring
      _ ≤ 1 := hDiv
  have hm : 0 ≤ mX beta hbeta.le :=
    (p4Q2PZ37AIW_originalNormalizedNegativeMargin_pos H beta hbeta).le
  have hmub : mX beta hbeta.le ≤ b * VX / 2 :=
    (p4Q2PZ37AIW_originalNormalizedNegativeMargin_bounds H beta hbeta.le).2
  have hmass :=
    p4Q2PZ37AJW_originalNegativeRegion_realMeasure_le_one H beta hbeta.le
  exact real_margin_probability_budget_le_sixteenth_ajx
    pX VX b (mX beta hbeta.le)
    (Measure.real muX
      {B : CfgX | uX beta hbeta.le B < -(mX beta hbeta.le)})
    hp hV.le hVcap hb hbp hm hmub hmass

/-- A hypothetical actual finite Wilson power below the original AJA
certificate MUST suppress its genuine source norm below V/16.
This is a necessary condition, not a constructed finite witness. -/
theorem p4Q2PZ37AJX_originalPower_budget_implies_sixteenth_source
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ)
    (hPower :
      ‖((SX beta hbeta.le) ^ n) fX‖ ^ 2 <
        (mX beta hbeta.le) ^ 2 *
          Measure.real muX
            {B : CfgX | uX beta hbeta.le B < -(mX beta hbeta.le)}) :
    ‖((SX beta hbeta.le) ^ n) fX‖ ^ 2 < VX / 16 :=
  hPower.trans_le
    (p4Q2PZ37AJX_originalAJA_certificate_le_sixteenth_variance
      H beta hbeta)

/-- Genuine whole-top energy is at most any true Wilson power energy.
Thus ANY AJA finite-power witness requires a direct top angular suppression. -/
theorem p4Q2PZ37AJX_originalPower_budget_implies_fullTop_sixteenth
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ)
    (hPower :
      ‖((SX beta hbeta.le) ^ n) fX‖ ^ 2 <
        (mX beta hbeta.le) ^ 2 *
          Measure.real muX
            {B : CfgX | uX beta hbeta.le B < -(mX beta hbeta.le)}) :
    ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 <
      VX / 16 := by
  have hTopPower :=
    p4Q2PZ37AJH_originalFullTop_norm_sq_le_transferPower H beta hbeta n
  exact hTopPower.trans_lt
    (p4Q2PZ37AJX_originalPower_budget_implies_sixteenth_source
      H beta hbeta n hPower)

/-- The selected unit top overlap cannot contain >=1/16 of source
variance if a true AJA finite-power witness exists. Other top directions
are not discarded. -/
theorem p4Q2PZ37AJX_originalPower_budget_implies_selectedOverlap_sixteenth
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ)
    (hPower :
      ‖((SX beta hbeta.le) ^ n) fX‖ ^ 2 <
        (mX beta hbeta.le) ^ 2 *
          Measure.real muX
            {B : CfgX | uX beta hbeta.le B < -(mX beta hbeta.le)}) :
    (inner ℝ fX (OmegaX beta hbeta.le)) ^ 2 < VX / 16 := by
  have hTop :=
    p4Q2PZ37AJX_originalPower_budget_implies_fullTop_sixteenth
      H beta hbeta n hPower
  have hSplit :=
    p4Q2PZ37AJF_originalSourceTop_norm_sq_eq_selected_add_extra H beta hbeta
  have hExtra0 :
      0 ≤ ‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ^ 2 :=
    sq_nonneg _
  linarith only [hTop, hSplit, hExtra0]

/-- Likewise the genuine ADDITIONAL full-top residual must itself have
less than 1/16 of the original source variance if an AJA witness exists. -/
theorem p4Q2PZ37AJX_originalPower_budget_implies_extraTop_sixteenth
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ)
    (hPower :
      ‖((SX beta hbeta.le) ^ n) fX‖ ^ 2 <
        (mX beta hbeta.le) ^ 2 *
          Measure.real muX
            {B : CfgX | uX beta hbeta.le B < -(mX beta hbeta.le)}) :
    ‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ^ 2 <
      VX / 16 := by
  have hTop :=
    p4Q2PZ37AJX_originalPower_budget_implies_fullTop_sixteenth
      H beta hbeta n hPower
  have hSplit :=
    p4Q2PZ37AJF_originalSourceTop_norm_sq_eq_selected_add_extra H beta hbeta
  have hSelected0 :
      0 ≤ (inner ℝ fX (OmegaX beta hbeta.le)) ^ 2 :=
    sq_nonneg _
  linarith only [hTop, hSplit, hSelected0]

/-- NECESSARY quantitative source angular separation: any actual AJA
power witness forces over fifteen sixteenths of the SOURCE variance
into the complete original top-orthogonal (excited) subspace. -/
theorem p4Q2PZ37AJX_originalPower_budget_implies_excitedSource_gt_fifteenSixteenths
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ)
    (hPower :
      ‖((SX beta hbeta.le) ^ n) fX‖ ^ 2 <
        (mX beta hbeta.le) ^ 2 *
          Measure.real muX
            {B : CfgX | uX beta hbeta.le B < -(mX beta hbeta.le)}) :
    15 * VX / 16 <
      ‖((TopX beta hbeta.le)ᗮ).starProjection fX‖ ^ 2 := by
  let S : PhysX →L[ℝ] PhysX := SX beta hbeta.le
  let F : Submodule ℝ PhysX := realHilbertTopEigenspace S
  letI : CompleteSpace F := (realHilbertTopEigenspace_isClosed S).completeSpace_coe
  letI : CompleteSpace Fᗮ := F.isClosed_orthogonal.completeSpace_coe
  have hTop :=
    p4Q2PZ37AJX_originalPower_budget_implies_fullTop_sixteenth
      H beta hbeta n hPower
  change ‖F.starProjection fX‖ ^ 2 < VX / 16 at hTop
  have hPyth := F.norm_sq_eq_add_norm_sq_starProjection fX
  simp only [F.starProjection_orthogonal_val] at hPyth
  have hVariance := p4Q2PZ37AJR_originalSource_norm_sq_eq_HaarVariance H
  have hExcited : 15 * VX / 16 < ‖(Fᗮ).starProjection fX‖ ^ 2 := by
    linarith only [hTop, hPyth, hVariance]
  change 15 * VX / 16 < ‖(Fᗮ).starProjection fX‖ ^ 2
  exact hExcited

/-- Direct numerical-top obstruction: a true full-top source fraction >=1/16
would exclude ALL positive finite-power witnesses for the genuine AJA budget.
No such large-top inequality is presumed to hold. -/
theorem p4Q2PZ37AJX_no_originalAJA_witness_of_large_fullTop
    (beta : ℝ) (hbeta : 0 < beta)
    (hTop :
      VX / 16 ≤
        ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2) :
    ¬ ∃ n : ℕ, 0 < n ∧
      ‖((SX beta hbeta.le) ^ n) fX‖ ^ 2 <
        (mX beta hbeta.le) ^ 2 *
          Measure.real muX
            {B : CfgX | uX beta hbeta.le B < -(mX beta hbeta.le)} := by
  rintro ⟨n, _hn, hPower⟩
  exact (not_lt_of_ge hTop)
    (p4Q2PZ37AJX_originalPower_budget_implies_fullTop_sixteenth
      H beta hbeta n hPower)

/-- Equivalent practical angular obstruction on the ORIGINAL excited
source: if its true orthogonal energy is <=15/16 of Haar variance, no
finite-power strict AJA witness can exist. The premise is NOT proved. -/
theorem p4Q2PZ37AJX_no_originalAJA_witness_of_small_excitedSource
    (beta : ℝ) (hbeta : 0 < beta)
    (hExcited :
      ‖((TopX beta hbeta.le)ᗮ).starProjection fX‖ ^ 2 ≤
        15 * VX / 16) :
    ¬ ∃ n : ℕ, 0 < n ∧
      ‖((SX beta hbeta.le) ^ n) fX‖ ^ 2 <
        (mX beta hbeta.le) ^ 2 *
          Measure.real muX
            {B : CfgX | uX beta hbeta.le B < -(mX beta hbeta.le)} := by
  rintro ⟨n, _hn, hPower⟩
  exact (not_lt_of_ge hExcited)
    (p4Q2PZ37AJX_originalPower_budget_implies_excitedSource_gt_fifteenSixteenths
      H beta hbeta n hPower)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

/-! Nine separate kernel axiom audits: no new axioms and no sorry. -/
#print axioms MGAP4D.MathlibAnalytic.real_margin_probability_budget_le_sixteenth_ajx
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJX_originalAJA_certificate_le_sixteenth_variance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJX_originalPower_budget_implies_sixteenth_source
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJX_originalPower_budget_implies_fullTop_sixteenth
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJX_originalPower_budget_implies_selectedOverlap_sixteenth
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJX_originalPower_budget_implies_extraTop_sixteenth
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJX_originalPower_budget_implies_excitedSource_gt_fifteenSixteenths
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJX_no_originalAJA_witness_of_large_fullTop
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJX_no_originalAJA_witness_of_small_excitedSource
