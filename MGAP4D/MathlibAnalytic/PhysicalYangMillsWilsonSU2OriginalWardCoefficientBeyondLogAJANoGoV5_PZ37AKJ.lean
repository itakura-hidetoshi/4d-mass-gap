import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalWardAffineLogarithmicAJANoGoV5_PZ37AKI
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AKJ — genuine Ward-coefficient obstruction above the logarithmic cutoff

New finite-H, physical-original, conditional non-witness region:
  1 <= 2 exp(-2 beta p_H) + exp(-beta p_H) r(beta)^4
=> NO strict original AJA power witness for beta>0.
Here r is the ORIGINAL ABN temporal character coefficient.

Unlike AKI, the positive affine term c=<original Ward crossing coefficient>
is NOT discarded when projecting the genuine SU(2) Wilson transfer onto the
existing nonnegative top vector. Its contribution strengthens the top lower
bound beyond the exponential d_H bound.

The new strict coefficient test is true at beta=kappa_H=log2/(2 p_H),
because the actual original temporal character r(kappa_H)>0.
ABN's already verified continuity then proves a NONEMPTY interval to the
RIGHT of kappa_H, containing a genuine beta>kappa_H with no original
AJA power witness. This does not assert absence for all beta>kappa_H.

The original source f0, full one-slab operator P, S=P/||P||, Haar measure,
AIG/AIW normalized negative region and margin, genuine full-top, roots,
hypotheses and pins are unchanged. No rank-one top or continuum gap claim.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped InnerProductSpace Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- A positive affine Ward coefficient cannot be ignored when turning
a negative top matrix coefficient into a lower squared-energy floor.
This is a pure scalar descent lemma, with the true physical hypotheses
supplied separately below. -/
theorem real_affine_top_overlap_le_negative_budget_akj
    (lambda c d I F m : ℝ)
    (hlambda : 0 < lambda) (_hc0 : 0 ≤ c) (hc : c ≤ lambda)
    (hd : 0 < d) (_hm : 0 ≤ m) (hMass : lambda ≤ I)
    (hPair : (lambda - c) * F ≤ -d * I)
    (hBudget : (lambda - c) * m ≤ d * lambda) :
    F ≤ -m := by
  have hI : 0 < I := hlambda.trans_le hMass
  have hGap : 0 < lambda - c := by
    by_contra hn
    have hz : lambda - c = 0 := le_antisymm (le_of_not_gt hn) (sub_nonneg.mpr hc)
    rw [hz, zero_mul] at hPair
    have hPos := mul_pos hd hI
    linarith only [hPair, hPos]
  have hdMass : d * lambda ≤ d * I :=
    mul_le_mul_of_nonneg_left hMass hd.le
  have hBound : d * lambda ≤ (lambda - c) * (-F) := by
    nlinarith only [hPair, hdMass]
  have hCombined : (lambda - c) * m ≤ (lambda - c) * (-F) :=
    hBudget.trans hBound
  by_contra hn
  have hGt : -m < F := lt_of_not_ge hn
  have hStrict : -F < m := by linarith only [hGt]
  have hMul := mul_lt_mul_of_pos_left hStrict hGap
  exact (not_lt_of_ge hCombined) hMul

local notation "GJ" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AKJ_group : IsTopologicalGroup GJ :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AKJ_compact : CompactSpace GJ :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AKJ_countable : SecondCountableTopology GJ :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AKJ_measurable : MeasurableSpace GJ :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AKJ_borel : BorelSpace GJ :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AKJ_links (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "CfgJ" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muJ" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "PhysJ" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "fJ" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "fcJ" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "VJ" => p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "pJ" => p4Q2PZ37AFZ_plaquetteCount H
local notation "PJ" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "SJ" => periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "psiJ" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector H 2 (by norm_num)
local notation "uJ" => p4Q2PZ37AIW_originalNormalizedSourceTransfer H
local notation "mJ" => p4Q2PZ37AIW_originalNormalizedNegativeMargin H
local notation "cJ" => p4Q2PZ37AKI_originalAffineCoefficient H
local notation "dJ" => p4Q2PZ37AKI_originalWardTopFloor H
local notation "rJ" => p4Q2PZ37ABN_originalTemporalWilsonCoefficient
local notation "ZJ" => p4Q2PZ37AIF_originalCrossingPartition H
local notation "kappaJ" => p4Q2PZ37AKI_logarithmicNoWitnessCutoff H

local instance p4Q2PZ37AKJ_probability : IsProbabilityMeasure muJ := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- A genuine coefficient comparison for the actual one-slab transfer,
using only existing original Haar and ABN data. -/
def p4Q2PZ37AKJ_WardEnhancedCriterion (beta : ℝ) : ℝ :=
  2 * Real.exp (-(2 * beta * pJ)) +
    Real.exp (-(beta * pJ)) * (rJ beta) ^ 4

/-- Keep the positive affine term: the true physical top matrix coefficient
satisfies the unweakened original Ward inequality for all beta>0. -/
theorem p4Q2PZ37AKJ_originalAffineTopPairing
    (beta : ℝ) (hbeta : 0 < beta) :
    (‖PJ beta hbeta.le‖ - cJ beta) *
        inner ℝ fJ (psiJ beta hbeta.le) ≤
      -(dJ beta) *
        ∫ A : CfgJ, ((psiJ beta hbeta.le : PhysJ) : Lp ℝ 2 muJ) A ∂muJ := by
  let P : PhysJ →L[ℝ] PhysJ := PJ beta hbeta.le
  let psi : PhysJ := psiJ beta hbeta.le
  let g : Lp ℝ 2 muJ := psi
  let c : ℝ := cJ beta
  let d : ℝ := dJ beta
  let I : ℝ := ∫ A : CfgJ, g A ∂muJ
  have hNonneg : ∀ᵐ A ∂muJ, 0 ≤ g A :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_ae_nonnegative
      H 2 (by norm_num) beta hbeta.le
  have hSource : (fun A : CfgJ => (fJ : Lp ℝ 2 muJ) A) =ᵐ[muJ] fcJ := by
    rw [p4Q2PZ37AFZ_originalCenteredSource_eq_toLp]
    exact ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := (2 : ENNReal)) (μ := muJ) fcJ
  have hRaw : ∀ᵐ A ∂muJ,
      (((P fJ : PhysJ) : Lp ℝ 2 muJ) - c • (fJ : Lp ℝ 2 muJ)) A ≤ -d := by
    filter_upwards [Lp.coeFn_sub ((P fJ : PhysJ) : Lp ℝ 2 muJ) (c • (fJ : Lp ℝ 2 muJ)),
      Lp.coeFn_smul c (fJ : Lp ℝ 2 muJ),
      p4Q2PZ37AIW_originalPhysicalTransfer_coeFn H beta hbeta.le fJ, hSource]
      with A hSub hSmul hPA hfA
    simp only [Pi.sub_apply] at hSub
    simp only [Pi.smul_apply, smul_eq_mul] at hSmul
    rw [hSub, hSmul, hPA, hfA]
    have h := p4Q2PZ37AKI_originalTransfer_affineUpper H beta hbeta A
    change decomposableOneSliceTransferIntegral H 2 beta fJ A -
      c * fcJ A ≤ -d
    linarith only [h]
  have hPair := realL2_inner_le_neg_floor_mul_mass_akg muJ
    (((P fJ : PhysJ) : Lp ℝ 2 muJ) - c • (fJ : Lp ℝ 2 muJ)) g d hRaw hNonneg
  change inner ℝ (P fJ - c • fJ) psi ≤ -d * I at hPair
  rw [inner_sub_left (𝕜 := ℝ) (P fJ : PhysJ) (c • fJ) psi,
    real_inner_smul_left (fJ : PhysJ) psi c] at hPair
  have hSymm : (P : PhysJ →ₗ[ℝ] PhysJ).IsSymmetric :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_isSymmetric
      H 2 (by norm_num) beta hbeta.le
  have hEigen : P psi = ‖P‖ • psi :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_eigen
      H 2 (by norm_num) beta hbeta.le
  have hEq : inner ℝ (P fJ) psi = ‖P‖ * inner ℝ fJ psi := by
    calc
      inner ℝ (P fJ) psi = inner ℝ fJ (P psi) := hSymm fJ psi
      _ = ‖P‖ * inner ℝ fJ psi := by
        rw [hEigen]
        exact real_inner_smul_right (fJ : PhysJ) psi ‖P‖
  rw [hEq] at hPair
  change (‖P‖ - c) * inner ℝ fJ psi ≤ -d * I
  nlinarith only [hPair]

/-- The still-positive, original temporal character improves the scalar
AKI cutoff whenever the criterion reaches one. No physical assumption is
added: beta is a variable in the true model. -/
theorem p4Q2PZ37AKJ_originalCoefficient_margin_compare
    (beta : ℝ) (hbeta : 0 < beta)
    (hCriterion : 1 ≤ p4Q2PZ37AKJ_WardEnhancedCriterion H beta) :
    (‖PJ beta hbeta.le‖ - cJ beta) * mJ beta hbeta.le ≤
      dJ beta * ‖PJ beta hbeta.le‖ := by
  let lambda : ℝ := ‖PJ beta hbeta.le‖
  let c : ℝ := cJ beta
  let d : ℝ := dJ beta
  let q : ℝ := Real.exp (-(beta * pJ))
  let e : ℝ := beta * q * VJ / 2
  have hq : 0 < q := Real.exp_pos _
  have hV : 0 < VJ := (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hR : 0 < rJ beta := p4Q2PZ37ABN_originalTemporalWilsonCoefficient_pos beta hbeta
  have hlambda : 0 < lambda :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) beta hbeta.le
  have hNormLe : lambda ≤ ZJ beta :=
    p4Q2PZ37AIV_originalPhysicalTransfer_norm_le_crossingPartition H beta hbeta.le
  have hc : 0 ≤ c ∧ c ≤ lambda :=
    p4Q2PZ37AKI_originalAffineCoefficient_bounds H beta hbeta
  have hq2 : q ^ 2 = Real.exp (-(2 * beta * pJ)) := by
    dsimp [q]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hq3 : q * q * q = Real.exp (-(3 * beta * pJ)) := by
    dsimp [q]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hCondition : 1 ≤ 2 * q ^ 2 + q * (rJ beta) ^ 4 := by
    change 1 ≤
      2 * Real.exp (-(2 * beta * pJ)) +
        Real.exp (-(beta * pJ)) * (rJ beta) ^ 4 at hCriterion
    rw [← hq2] at hCriterion
    exact hCriterion
  have hNonnegR : 0 ≤ q * (rJ beta) ^ 4 := by positivity
  have hCLower : lambda * (q * (rJ beta) ^ 4) ≤ c := by
    calc
      lambda * (q * (rJ beta) ^ 4) ≤ ZJ beta * (q * (rJ beta) ^ 4) :=
        mul_le_mul_of_nonneg_right hNormLe hNonnegR
      _ = c := by
        dsimp [c, p4Q2PZ37AKI_originalAffineCoefficient, q]
        ring
  have hScaled :=
    mul_le_mul_of_nonneg_right hCondition hlambda.le
  have hGap : lambda - c ≤ (2 * q ^ 2) * lambda := by
    nlinarith only [hCLower, hScaled]
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hm : mJ beta hbeta.le ≤ e := by
    have h := (p4Q2PZ37AIW_originalNormalizedNegativeMargin_bounds H beta hbeta.le).2
    change mJ beta hbeta.le ≤ beta * q * VJ / 2 at h
    exact h
  have hGap0 : 0 ≤ lambda - c := sub_nonneg.mpr hc.2
  change (lambda - c) * mJ beta hbeta.le ≤ d * lambda
  calc
    (lambda - c) * mJ beta hbeta.le ≤
        (lambda - c) * e := mul_le_mul_of_nonneg_left hm hGap0
    _ ≤ ((2 * q ^ 2) * lambda) * e :=
      mul_le_mul_of_nonneg_right hGap he
    _ = d * lambda := by
      dsimp [e, d, p4Q2PZ37AKI_originalWardTopFloor]
      rw [← hq3]
      ring

/-- The ACTUAL source has enough top overlap to block the original
AJA certificate under the stated original Ward coefficient test. -/
theorem p4Q2PZ37AKJ_originalTop_overlap_le_negative_originalMargin
    (beta : ℝ) (hbeta : 0 < beta)
    (hCriterion : 1 ≤ p4Q2PZ37AKJ_WardEnhancedCriterion H beta) :
    inner ℝ fJ (psiJ beta hbeta.le) ≤ -(mJ beta hbeta.le) := by
  let lambda : ℝ := ‖PJ beta hbeta.le‖
  let c : ℝ := cJ beta
  let d : ℝ := dJ beta
  let I : ℝ :=
    ∫ A : CfgJ, ((psiJ beta hbeta.le : PhysJ) : Lp ℝ 2 muJ) A ∂muJ
  let F : ℝ := inner ℝ fJ (psiJ beta hbeta.le)
  let m : ℝ := mJ beta hbeta.le
  have hlambda : 0 < lambda :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) beta hbeta.le
  have hc : 0 ≤ c ∧ c ≤ lambda :=
    p4Q2PZ37AKI_originalAffineCoefficient_bounds H beta hbeta
  have hV : 0 < VJ := (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hd : 0 < d := by dsimp [d, p4Q2PZ37AKI_originalWardTopFloor]; positivity
  have hm : 0 ≤ m :=
    (p4Q2PZ37AIW_originalNormalizedNegativeMargin_pos H beta hbeta).le
  have hMass : lambda ≤ I :=
    p4Q2PZ37AKG_originalNonnegativeTop_mass_ge_norm H beta hbeta.le
  have hPair : (lambda - c) * F ≤ -d * I :=
    p4Q2PZ37AKJ_originalAffineTopPairing H beta hbeta
  have hBudget : (lambda - c) * m ≤ d * lambda :=
    p4Q2PZ37AKJ_originalCoefficient_margin_compare H beta hbeta hCriterion
  exact real_affine_top_overlap_le_negative_budget_akj
    lambda c d I F m hlambda hc.1 hc.2 hd hm hMass hPair hBudget

/-- The original strict AJA power witness is excluded on the NEW
coefficient-defined region, not just on beta<=log2/(2 p_H). -/
theorem p4Q2PZ37AKJ_originalWardEnhanced_no_AJA_power_witness
    (beta : ℝ) (hbeta : 0 < beta)
    (hCriterion : 1 ≤ p4Q2PZ37AKJ_WardEnhancedCriterion H beta) :
    ¬ ∃ n : ℕ, ‖((SJ beta hbeta.le) ^ n) fJ‖ ^ 2 <
      (mJ beta hbeta.le) ^ 2 *
        Measure.real muJ
          {A : CfgJ | uJ beta hbeta.le A < -(mJ beta hbeta.le)} := by
  let P : PhysJ →L[ℝ] PhysJ := PJ beta hbeta.le
  let S : PhysJ →L[ℝ] PhysJ := SJ beta hbeta.le
  let psi : PhysJ := psiJ beta hbeta.le
  let m : ℝ := mJ beta hbeta.le
  have hPositive : 0 ≤ m :=
    (p4Q2PZ37AIW_originalNormalizedNegativeMargin_pos H beta hbeta).le
  have hUnit : ‖psi‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_norm
      H 2 (by norm_num) beta hbeta.le
  have hNorm : 0 < ‖P‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) beta hbeta.le
  have hEigen : P psi = ‖P‖ • psi :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_eigen
      H 2 (by norm_num) beta hbeta.le
  have hFix : S psi = psi := by
    change ‖P‖⁻¹ • P psi = psi
    rw [hEigen, smul_smul, inv_mul_cancel₀ hNorm.ne', one_smul]
  have hSymm : (S : PhysJ →ₗ[ℝ] PhysJ).IsSymmetric :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H 2 (by norm_num) beta hbeta.le
  have hF : inner ℝ fJ psi ≤ -m :=
    p4Q2PZ37AKJ_originalTop_overlap_le_negative_originalMargin H beta hbeta hCriterion
  have hR : Measure.real muJ
      {A : CfgJ | uJ beta hbeta.le A < -(mJ beta hbeta.le)} ≤ 1 := by
    have h := ENNReal.toReal_mono (measure_ne_top muJ Set.univ)
      (measure_mono (Set.subset_univ
        {A : CfgJ | uJ beta hbeta.le A < -(mJ beta hbeta.le)}))
    simpa only [Measure.real, measure_univ, ENNReal.toReal_one] using h
  rintro ⟨n, hn⟩
  have hBudget : (mJ beta hbeta.le) ^ 2 *
        Measure.real muJ
          {A : CfgJ | uJ beta hbeta.le A < -(mJ beta hbeta.le)} ≤
        m ^ 2 := by
    simpa [m] using mul_le_mul_of_nonneg_left hR (sq_nonneg (mJ beta hbeta.le))
  have hFloor : m ^ 2 ≤ ‖((SJ beta hbeta.le) ^ n) fJ‖ ^ 2 :=
    realHilbert_fixedUnit_power_normSq_ge_neg_overlap_akg S hSymm psi hUnit hFix
      fJ m hPositive hF n
  exact (not_lt_of_ge (hBudget.trans hFloor)) hn

/-- The Ward-enhanced original coefficient condition is continuous
in the ACTUAL coupling; original ABN integrals were already certified. -/
theorem p4Q2PZ37AKJ_WardEnhancedCriterion_continuous :
    Continuous (p4Q2PZ37AKJ_WardEnhancedCriterion H) := by
  have hExp2 : Continuous (fun beta : ℝ => Real.exp (-(2 * beta * pJ))) :=
    Real.continuous_exp.comp (by fun_prop)
  have hExp1 : Continuous (fun beta : ℝ => Real.exp (-(beta * pJ))) :=
    Real.continuous_exp.comp (by fun_prop)
  have hr : Continuous (fun beta : ℝ => (rJ beta) ^ 4) :=
    (p4Q2PZ37ABN_originalTemporalWilsonCoefficient_continuous).pow 4
  change Continuous (fun beta : ℝ =>
    2 * Real.exp (-(2 * beta * pJ)) +
      Real.exp (-(beta * pJ)) * (rJ beta) ^ 4)
  exact (continuous_const.mul hExp2).add (hExp1.mul hr)

/-- At the ORIGINAL logarithmic endpoint, the old comparison
2*exp(-2 beta p)=1 is sharpened strictly by the actual r(beta)^4>0. -/
theorem p4Q2PZ37AKJ_WardEnhancedCriterion_gt_one_at_logarithmic :
    1 < p4Q2PZ37AKJ_WardEnhancedCriterion H kappaJ := by
  have hp : 0 < pJ := p4Q2PZ37AHN_count_pos H
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hk : 0 < kappaJ := by
    unfold p4Q2PZ37AKI_logarithmicNoWitnessCutoff
    exact div_pos hlog (by positivity)
  have hkEq : 2 * kappaJ * pJ = Real.log 2 := by
    unfold p4Q2PZ37AKI_logarithmicNoWitnessCutoff
    field_simp
  have hExp : Real.exp (-(2 * kappaJ * pJ)) = (1 / 2 : ℝ) := by
    rw [hkEq, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hr : 0 < rJ kappaJ :=
    p4Q2PZ37ABN_originalTemporalWilsonCoefficient_pos kappaJ hk
  have hTerm : 0 < Real.exp (-(kappaJ * pJ)) * (rJ kappaJ) ^ 4 :=
    mul_pos (Real.exp_pos _) (pow_pos hr 4)
  change 1 < 2 * Real.exp (-(2 * kappaJ * pJ)) +
    Real.exp (-(kappaJ * pJ)) * (rJ kappaJ) ^ 4
  rw [hExp]
  linarith only [hTerm]

/-- Because the actual r(beta) is continuous and strictly positive at
kappa_H, some explicit existential coupling strictly ABOVE kappa_H
still has NO genuine original AJA finite-power witness. -/
theorem p4Q2PZ37AKJ_exists_above_logarithmic_no_AJA_power_witness :
    ∃ beta : ℝ, ∃ hbeta : 0 < beta, kappaJ < beta ∧
      ¬ ∃ n : ℕ, ‖((SJ beta hbeta.le) ^ n) fJ‖ ^ 2 <
        (mJ beta hbeta.le) ^ 2 *
          Measure.real muJ
            {A : CfgJ | uJ beta hbeta.le A < -(mJ beta hbeta.le)} := by
  have hOpen : IsOpen {beta : ℝ | 1 < p4Q2PZ37AKJ_WardEnhancedCriterion H beta} :=
    isOpen_Ioi.preimage (p4Q2PZ37AKJ_WardEnhancedCriterion_continuous H)
  have hEndpoint :
      kappaJ ∈ {beta : ℝ | 1 < p4Q2PZ37AKJ_WardEnhancedCriterion H beta} :=
    p4Q2PZ37AKJ_WardEnhancedCriterion_gt_one_at_logarithmic H
  obtain ⟨epsilon, hepsilon, hBall⟩ :=
    (Metric.isOpen_iff.mp hOpen) kappaJ hEndpoint
  let beta : ℝ := kappaJ + epsilon / 2
  have hGreater : kappaJ < beta := by dsimp [beta]; linarith only [hepsilon]
  have hk : 0 < kappaJ := by
    have hp : 0 < pJ := p4Q2PZ37AHN_count_pos H
    unfold p4Q2PZ37AKI_logarithmicNoWitnessCutoff
    exact div_pos (Real.log_pos (by norm_num)) (by positivity)
  have hbeta : 0 < beta := hk.trans hGreater
  have hBallMem : beta ∈ Metric.ball kappaJ epsilon := by
    rw [Metric.mem_ball, Real.dist_eq]
    have hDiff : beta - kappaJ = epsilon / 2 := by dsimp [beta]; ring
    rw [hDiff, abs_of_pos (by linarith only [hepsilon])]
    linarith only [hepsilon]
  have hCriterion : 1 ≤ p4Q2PZ37AKJ_WardEnhancedCriterion H beta :=
    (hBall hBallMem).le
  refine ⟨beta, hbeta, hGreater, ?_⟩
  exact p4Q2PZ37AKJ_originalWardEnhanced_no_AJA_power_witness
    H beta hbeta hCriterion

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

/-! Kernel axiom audits: unchanged original three standard axioms only. -/
#print axioms MGAP4D.MathlibAnalytic.real_affine_top_overlap_le_negative_budget_akj
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKJ_WardEnhancedCriterion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKJ_originalAffineTopPairing
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKJ_originalCoefficient_margin_compare
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKJ_originalTop_overlap_le_negative_originalMargin
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKJ_originalWardEnhanced_no_AJA_power_witness
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKJ_WardEnhancedCriterion_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKJ_WardEnhancedCriterion_gt_one_at_logarithmic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKJ_exists_above_logarithmic_no_AJA_power_witness
