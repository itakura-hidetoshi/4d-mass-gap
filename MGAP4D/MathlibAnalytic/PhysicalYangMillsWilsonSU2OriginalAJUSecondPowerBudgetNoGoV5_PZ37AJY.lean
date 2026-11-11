import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalAJAAbsoluteSixteenthSectorCriterionV5_PZ37AJX
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AJY — obstruction for AJU's *sufficient* n=2 AJA threshold

The AJU physical source, symmetric Wilson transfer, true orthogonal
restriction q, rational Haar variance defect floor d, and original
AJA Haar certificate B are unchanged.

From AIK's actual lower variance witness v <= V, AIS's original variance
cap V <= p^2/4, and b*p <= 1 for b=beta*exp(-beta*p), obtain d^2 <= V/4.
For q >= 0 the AJU correction C2=(1-q^4)*(d/(1+q))^2 <= d^2.
The certified AJX certificate B <= V/16 consequently obeys

  B + C2 <= 5*V/16 < V.

Thus AJU's particular SUFFICIENT condition V-C2 < B is impossible at
every fixed finite H and beta>0. This DOES NOT prove that the actual
Wilson second-power norm is >= B, nor that no finite AJA witness exists:
AJU's estimated upper bound may be loose. No original physical
assumption, Hilbert top multiplicity, Haar normalization, pin or root
is changed.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- The AJU two-power correction is never bigger than the square of its
underlying one-step defect floor. This is a pure real inequality and makes
no assertion about the true second Wilson power. -/
theorem real_secondPower_correction_le_defect_sq_ajy
    (q d : ℝ) (hq : 0 ≤ q) (hd : 0 ≤ d) :
    (1 - q ^ 4) * (d / (1 + q)) ^ 2 ≤ d ^ 2 := by
  have hden : 0 < 1 + q := by linarith only [hq]
  have hratio : d / (1 + q) ≤ d := by
    apply (div_le_iff₀ hden).2
    have hprod : 0 ≤ d * q := mul_nonneg hd hq
    nlinarith only [hprod]
  have hratio0 : 0 ≤ d / (1 + q) := div_nonneg hd hden.le
  have hratioSq : (d / (1 + q)) ^ 2 ≤ d ^ 2 :=
    (sq_le_sq₀ hratio0 hd).2 hratio
  have hfac : 1 - q ^ 4 ≤ 1 := by
    have hqPow : 0 ≤ q ^ 4 := pow_nonneg hq 4
    linarith only [hqPow]
  calc
    (1 - q ^ 4) * (d / (1 + q)) ^ 2 ≤
        1 * (d / (1 + q)) ^ 2 :=
      mul_le_mul_of_nonneg_right hfac (sq_nonneg _)
    _ ≤ d ^ 2 := by simpa only [one_mul] using hratioSq

/-- The genuine AIK/AIW/AIS numerical information alone bounds the
*chosen lower defect floor* by one-quarter of the source variance in
square. No inference about the actual full-top energy is made. -/
theorem real_defect_floor_sq_le_variance_quarter_ajy
    (p V v b d : ℝ)
    (hp : 0 < p) (hV : 0 < V)
    (hVcap : V ≤ p ^ 2 / 4)
    (hb : 0 ≤ b) (hbp : b * p ≤ 1)
    (hvV : v ≤ V) (hd0 : 0 ≤ d) (hdub : d ≤ b * v) :
    d ^ 2 ≤ V / 4 := by
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
    have h := mul_le_mul_of_nonneg_right hQuarter hV.le
    nlinarith only [h]
  have hD : d ≤ b * V :=
    hdub.trans (mul_le_mul_of_nonneg_left hvV hb)
  have hDSq : d ^ 2 ≤ (b * V) ^ 2 :=
    (sq_le_sq₀ hd0 (mul_nonneg hb hV.le)).2 hD
  exact hDSq.trans hPowerBound

local notation "GY" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AJY_group : IsTopologicalGroup GY :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AJY_compact : CompactSpace GY :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AJY_secondCountable : SecondCountableTopology GY :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AJY_measurable : MeasurableSpace GY :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AJY_borel : BorelSpace GY :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AJY_linkFintype (K : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink K) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "CfgY" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muY" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "VY" =>
  p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "pY" =>
  p4Q2PZ37AFZ_plaquetteCount H
local notation "vY" =>
  p4Q2PZ37AIK_elementarySourceVarianceFloor H
local notation "uY" =>
  p4Q2PZ37AIW_originalNormalizedSourceTransfer H
local notation "mY" =>
  p4Q2PZ37AIW_originalNormalizedNegativeMargin H
local notation "dY" =>
  p4Q2PZ37AJU_originalDefectFloor H
local notation "RY" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator H 2 (by norm_num)

/-- The correction in AJU's EXACT n=2 upper bound is at most one-quarter
of the original source Haar variance at each H,beta>0. The actual
second-power norm is NOT identified with this bound. -/
theorem p4Q2PZ37AJY_originalAJU_twoPowerCorrection_le_quarter_variance
    (beta : ℝ) (hbeta : 0 < beta) :
    p4Q2PZ37AJU_originalTwoPowerCorrection H beta hbeta.le ≤ VY / 4 := by
  let b : ℝ := beta * Real.exp (-(beta * pY))
  have hp : 0 < pY := p4Q2PZ37AHN_count_pos H
  have hV : 0 < VY :=
    (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hVcap : VY ≤ pY ^ 2 / 4 :=
    p4Q2PZ37AIS_originalSourceSecondMoment_le_countSquare H
  have hb : 0 ≤ b := by
    dsimp [b]
    positivity
  have hbp : b * pY ≤ 1 := by
    have hExp : beta * pY ≤ Real.exp (beta * pY) := by
      linarith only [Real.add_one_le_exp (beta * pY)]
    have hDiv : beta * pY / Real.exp (beta * pY) ≤ 1 :=
      (div_le_iff₀ (Real.exp_pos _)).2 (by linarith only [hExp])
    calc
      b * pY = beta * pY / Real.exp (beta * pY) := by
        dsimp [b]
        rw [Real.exp_neg]
        ring
      _ ≤ 1 := hDiv
  have hvV : vY ≤ VY :=
    p4Q2PZ37AIK_elementarySourceVarianceFloor_le_original H
  have hd0 : 0 ≤ dY beta :=
    (p4Q2PZ37AJU_originalDefectFloor_pos H beta hbeta).le
  have hdub : dY beta ≤ b * vY := by
    apply le_of_eq
    unfold p4Q2PZ37AJU_originalDefectFloor
    dsimp [b]
    rw [Real.exp_neg]
    ring
  have hCorrection :
      p4Q2PZ37AJU_originalTwoPowerCorrection H beta hbeta.le ≤ (dY beta) ^ 2 := by
    have hq0 : 0 ≤ ‖RY beta hbeta.le‖ :=
      norm_nonneg (RY beta hbeta.le)
    have hRaw := real_secondPower_correction_le_defect_sq_ajy
      ‖RY beta hbeta.le‖ (dY beta) hq0 hd0
    change
      p4Q2PZ37AJU_originalTwoPowerCorrection H beta hbeta.le ≤ (dY beta) ^ 2
      at hRaw
    exact hRaw
  exact hCorrection.trans
    (real_defect_floor_sq_le_variance_quarter_ajy
      pY VY vY b (dY beta) hp hV hVcap hb hbp hvV hd0 hdub)

/-- Joint quantitative obstruction, using the TRUE AJA certificate
rather than a surrogate margin. The combined quantities take at most
5/16 of the source variance, hence cannot exceed the whole source. -/
theorem p4Q2PZ37AJY_originalAJA_add_AJU_correction_le_fiveSixteenths
    (beta : ℝ) (hbeta : 0 < beta) :
    (mY beta hbeta.le) ^ 2 *
      Measure.real muY
        {B : CfgY | uY beta hbeta.le B < -(mY beta hbeta.le)} +
      p4Q2PZ37AJU_originalTwoPowerCorrection H beta hbeta.le ≤
        5 * VY / 16 := by
  have hCertificate :=
    p4Q2PZ37AJX_originalAJA_certificate_le_sixteenth_variance
      H beta hbeta
  have hCorrection :=
    p4Q2PZ37AJY_originalAJU_twoPowerCorrection_le_quarter_variance
      H beta hbeta
  linarith only [hCertificate, hCorrection]

/-- The actual AJA Haar certificate lies STRICTLY below the AJU
n=2 *estimated upper threshold*. This says nothing by itself about
the true source transfer power, whose upper estimate can be loose. -/
theorem p4Q2PZ37AJY_originalAJA_below_AJU_secondPower_upper
    (beta : ℝ) (hbeta : 0 < beta) :
    (mY beta hbeta.le) ^ 2 *
      Measure.real muY
        {B : CfgY | uY beta hbeta.le B < -(mY beta hbeta.le)} <
      VY - p4Q2PZ37AJU_originalTwoPowerCorrection H beta hbeta.le := by
  have hSum :=
    p4Q2PZ37AJY_originalAJA_add_AJU_correction_le_fiveSixteenths
      H beta hbeta
  have hV : 0 < VY :=
    (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  linarith only [hSum, hV]

/-- The particular sufficient strict-threshold premise in AJU is
IMPOSSIBLE with the original definitions. This is not a statement
that ||S^2 f0||^2 < B itself is impossible. -/
theorem p4Q2PZ37AJY_originalAJU_secondPower_sufficient_threshold_impossible
    (beta : ℝ) (hbeta : 0 < beta) :
    ¬ (VY - p4Q2PZ37AJU_originalTwoPowerCorrection H beta hbeta.le <
      (mY beta hbeta.le) ^ 2 *
        Measure.real muY
          {B : CfgY | uY beta hbeta.le B < -(mY beta hbeta.le)}) := by
  exact not_lt_of_ge
    (le_of_lt
      (p4Q2PZ37AJY_originalAJA_below_AJU_secondPower_upper H beta hbeta))

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

/-! Six kernel axiom audits: no added axioms, no sorry. -/
#print axioms MGAP4D.MathlibAnalytic.real_secondPower_correction_le_defect_sq_ajy
#print axioms MGAP4D.MathlibAnalytic.real_defect_floor_sq_le_variance_quarter_ajy
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJY_originalAJU_twoPowerCorrection_le_quarter_variance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJY_originalAJA_add_AJU_correction_le_fiveSixteenths
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJY_originalAJA_below_AJU_secondPower_upper
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJY_originalAJU_secondPower_sufficient_threshold_impossible
