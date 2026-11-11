import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalQFreeFullTopVarianceV5_PZ37AJV
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AJW — genuine AJA budget vs AJV q-free correction: strict obstruction

This append-only leaf COMPARES the original finite-H, beta>0 Wilson/Haar
quantities without changing any physical definition, root, normalization,
variance, certified positive Haar region, or Lean/mathlib pin.

The true AJA certificate is B=m^2*mu({u < -m}); the true AJV correction
is c=(d/2)^2. The old AJV sufficient condition V-c < B was never proved.

The *existing* AIW bound m <= beta*exp(-beta*p)*V/2, the original
AIK variance lower bound v<=V, the AIS upper bound V<=p^2/4,
the original AJU identity d=beta*exp(-beta*p)*v, and normalized Haar
probability mass <=1 together force

  B + c <= V/8 < V,  hence  B < V-c.

In particular the specific AJV sufficient threshold is impossible at
EVERY finite H, beta>0. This does NOT rule out genuine finite-power
witnesses by a sharper argument: AJV's upper bound need not be sharp.
The actual top norm or true finite-power norm may lie below B even
though this coarse sufficient test fails. No top rank-one, uniform
coercivity, Hamiltonian gap, or continuum mass gap is claimed.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Real-algebraic obstruction, independent of any surrogate physical model.
If b*p <= 1, 0<V<=p²/4, v<=V, m<=bV/2, d<=bv, and
mass<=1, then the margin certificate plus q-free deficit correction
takes at most one eighth of V. -/
theorem real_margin_defect_budget_eighth_bound_ajw
    (p V v b m d mass : ℝ)
    (hp : 0 < p) (hV : 0 < V)
    (hVcap : V ≤ p ^ 2 / 4)
    (hb : 0 ≤ b) (hbp : b * p ≤ 1)
    (hm : 0 ≤ m) (hmub : m ≤ b * V / 2)
    (hd : 0 ≤ d) (hdub : d ≤ b * v)
    (hvV : v ≤ V)
    (hmass : mass ≤ 1) :
    m ^ 2 * mass + (d / 2) ^ 2 ≤ V / 8 := by
  have hbp0 : 0 ≤ b * p := mul_nonneg hb hp.le
  have hbp2 : (b * p) ^ 2 ≤ (1 : ℝ) := by
    simpa only [one_pow] using (sq_le_sq₀ hbp0 (by norm_num)).2 hbp
  have hbp2' : b ^ 2 * p ^ 2 ≤ (1 : ℝ) := by
    nlinarith only [hbp2]
  have hScaledV : b ^ 2 * V ≤ b ^ 2 * (p ^ 2 / 4) :=
    mul_le_mul_of_nonneg_left hVcap (sq_nonneg b)
  have hScaledQuarter : b ^ 2 * V ≤ (1 : ℝ) / 4 := by
    nlinarith only [hScaledV, hbp2']
  have hPowerBound : (b * V) ^ 2 ≤ V / 4 := by
    have h := mul_le_mul_of_nonneg_right hScaledQuarter hV.le
    nlinarith only [h]
  have hBhalf : 0 ≤ b * V / 2 := by positivity
  have hmSq : m ^ 2 ≤ (b * V / 2) ^ 2 :=
    (sq_le_sq₀ hm hBhalf).2 hmub
  have hdub' : d ≤ b * V :=
    hdub.trans (mul_le_mul_of_nonneg_left hvV hb)
  have hdHalf : d / 2 ≤ b * V / 2 := by
    linarith only [hdub']
  have hdSq : (d / 2) ^ 2 ≤ (b * V / 2) ^ 2 :=
    (sq_le_sq₀ (by positivity) hBhalf).2 hdHalf
  have hMarginMass : m ^ 2 * mass ≤ m ^ 2 := by
    calc
      m ^ 2 * mass ≤ m ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hmass (sq_nonneg m)
      _ = m ^ 2 := by ring
  nlinarith only [hMarginMass, hmSq, hdSq, hPowerBound]

local notation "GW" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AJW_group : IsTopologicalGroup GW :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AJW_compact : CompactSpace GW :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AJW_secondCountable : SecondCountableTopology GW :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AJW_measurable : MeasurableSpace GW :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AJW_borel : BorelSpace GW :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AJW_linkFintype (K : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink K) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "CfgW" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muW" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "VW" =>
  p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "pW" =>
  p4Q2PZ37AFZ_plaquetteCount H
local notation "vW" =>
  p4Q2PZ37AIK_elementarySourceVarianceFloor H
local notation "uW" =>
  p4Q2PZ37AIW_originalNormalizedSourceTransfer H
local notation "mW" =>
  p4Q2PZ37AIW_originalNormalizedNegativeMargin H
local notation "dW" =>
  p4Q2PZ37AJU_originalDefectFloor H

local instance p4Q2PZ37AJW_probability : IsProbabilityMeasure muW := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- The unchanged AJA region has REAL Haar probability at most one. -/
theorem p4Q2PZ37AJW_originalNegativeRegion_realMeasure_le_one
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Measure.real muW
      {B : CfgW | uW beta hbeta B < -(mW beta hbeta)} ≤ 1 := by
  let s : Set CfgW := {B : CfgW | uW beta hbeta B < -(mW beta hbeta)}
  have hmassEN : muW s ≤ (1 : ENNReal) := by
    calc
      muW s ≤ muW Set.univ := measure_mono (Set.subset_univ s)
      _ = 1 := measure_univ
  have hmassReal : (muW s).toReal ≤ (1 : ENNReal).toReal :=
    ENNReal.toReal_mono (by simp) hmassEN
  simpa only [s, Measure.real, ENNReal.toReal_one] using hmassReal

/-- The ACTUAL original AJA quantitative Haar-L² budget and AJV
q-free geometric correction sum to at most one eighth of the same
genuine centered-source Haar variance, for every finite H and beta>0. -/
theorem p4Q2PZ37AJW_originalAJA_add_qfree_le_eighth_variance
    (beta : ℝ) (hbeta : 0 < beta) :
    (mW beta hbeta.le) ^ 2 *
      Measure.real muW
        {B : CfgW | uW beta hbeta.le B < -(mW beta hbeta.le)} +
      p4Q2PZ37AJV_originalQFreeCorrection H beta ≤ VW / 8 := by
  let b : ℝ := beta * Real.exp (-(beta * pW))
  have hp : 0 < pW := p4Q2PZ37AHN_count_pos H
  have hV : 0 < VW := (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hVcap : VW ≤ pW ^ 2 / 4 :=
    p4Q2PZ37AIS_originalSourceSecondMoment_le_countSquare H
  have hb : 0 ≤ b := by
    dsimp [b]
    positivity
  have hbp : b * pW ≤ 1 := by
    have hExp : beta * pW ≤ Real.exp (beta * pW) := by
      linarith only [Real.add_one_le_exp (beta * pW)]
    have hDiv : beta * pW / Real.exp (beta * pW) ≤ 1 :=
      (div_le_iff₀ (Real.exp_pos _)).2 (by linarith only [hExp])
    calc
      b * pW = beta * pW / Real.exp (beta * pW) := by
        dsimp [b]
        rw [Real.exp_neg]
        ring
      _ ≤ 1 := hDiv
  have hm : 0 ≤ mW beta hbeta.le :=
    (p4Q2PZ37AIW_originalNormalizedNegativeMargin_pos H beta hbeta).le
  have hmub : mW beta hbeta.le ≤ b * VW / 2 :=
    (p4Q2PZ37AIW_originalNormalizedNegativeMargin_bounds H beta hbeta.le).2
  have hd : 0 ≤ dW beta :=
    (p4Q2PZ37AJU_originalDefectFloor_pos H beta hbeta).le
  have hdub : dW beta ≤ b * vW := by
    apply le_of_eq
    unfold p4Q2PZ37AJU_originalDefectFloor
    dsimp [b]
    rw [Real.exp_neg]
    ring
  have hvV : vW ≤ VW :=
    p4Q2PZ37AIK_elementarySourceVarianceFloor_le_original H
  have hmass :=
    p4Q2PZ37AJW_originalNegativeRegion_realMeasure_le_one H beta hbeta.le
  have hBound :=
    real_margin_defect_budget_eighth_bound_ajw
      pW VW vW b (mW beta hbeta.le) (dW beta)
      (Measure.real muW
        {B : CfgW | uW beta hbeta.le B < -(mW beta hbeta.le)})
      hp hV hVcap hb hbp hm hmub hd hdub hvV hmass
  simpa only [p4Q2PZ37AJV_originalQFreeCorrection] using hBound

/-- Strict REVERSE comparison: the q-free AJV upper bound V-c is ALWAYS
larger than the genuine AJA certificate B for finite H, positive beta. -/
theorem p4Q2PZ37AJW_originalAJA_strictly_below_qfree_upper
    (beta : ℝ) (hbeta : 0 < beta) :
    (mW beta hbeta.le) ^ 2 *
      Measure.real muW
        {B : CfgW | uW beta hbeta.le B < -(mW beta hbeta.le)} <
      VW - p4Q2PZ37AJV_originalQFreeCorrection H beta := by
  have hBound :=
    p4Q2PZ37AJW_originalAJA_add_qfree_le_eighth_variance H beta hbeta
  have hV : 0 < VW := (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  linarith only [hBound, hV]

/-- The exact specific AJV sufficient threshold is impossible for ANY
finite H and beta>0 in the original Wilson model. This does NOT disprove
an independently established AJA witness or actual smallness of top. -/
theorem p4Q2PZ37AJW_originalAJV_qfreeAJA_threshold_impossible
    (beta : ℝ) (hbeta : 0 < beta) :
    ¬ (VW - p4Q2PZ37AJV_originalQFreeCorrection H beta <
      (mW beta hbeta.le) ^ 2 *
        Measure.real muW
          {B : CfgW | uW beta hbeta.le B < -(mW beta hbeta.le)}) := by
  exact not_lt_of_ge
    (le_of_lt (p4Q2PZ37AJW_originalAJA_strictly_below_qfree_upper
      H beta hbeta))

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

/-! Five new declarations: independent full axiom audit. -/
#print axioms MGAP4D.MathlibAnalytic.real_margin_defect_budget_eighth_bound_ajw
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJW_originalNegativeRegion_realMeasure_le_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJW_originalAJA_add_qfree_le_eighth_variance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJW_originalAJA_strictly_below_qfree_upper
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJW_originalAJV_qfreeAJA_threshold_impossible
