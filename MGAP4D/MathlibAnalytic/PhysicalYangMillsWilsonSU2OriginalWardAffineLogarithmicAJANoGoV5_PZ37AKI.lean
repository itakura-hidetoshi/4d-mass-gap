import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalOutsideAILCubicAJANoGoV5_PZ37AKH
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalWardCrossingHalfHaarUnitCouplingV5_PZ37AIS
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AKI — original Ward affine floor beyond the cubic interval

This leaf retains the true finite-H Wilson P, S=P/||P||, signed ZW f0,
Haar probability, old source representative fc=(W-p)/2 and AJA budget B.
Unlike AKG/AKH it does NOT assume the raw source image is everywhere negative.
AIN's signed quadratic estimate and AIS's genuine Ward moment floor give
  P f0(A) <= c*fc(A)-d,
  c=Zcross*exp(-beta*p)*r(beta)^4,  d=beta*exp(-3*beta*p)*V.
ABN and AIW prove 0<=c<=||P||. Pairing with the genuine nonnegative unit
top vector gives F=<f0,psi><0 and then F<=-d, since its Haar mass I>=||P||.
Thus every actual normalized power has energy >=d^2 for ALL beta>0.

The ORIGINAL AJA certificate satisfies B<=(beta*exp(-beta*p)*V/2)^2.
Consequently no strict witness exists for 0<beta<=log(2)/(2*p), including
the endpoint. This cutoff strictly exceeds the old AIM theta_H. At H=0 it
also exceeds the ORIGINAL fixed beta0=log(3/2)/64, deciding that fixed
coupling in the minimal original finite volume, not in all volumes.

The auxiliary scalars below do not redefine any old physical quantity.
No top simplicity, extra physical assumption, altered source/budget,
H-uniform coercivity, Hamiltonian or continuum mass gap is asserted.
All claims in this new leaf await exact-source kernel CI.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory Filter
open scoped InnerProductSpace Topology Classical ENNReal
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "GI" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AKI_group : IsTopologicalGroup GI := specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AKI_compact : CompactSpace GI := specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AKI_countable : SecondCountableTopology GI := specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AKI_measurable : MeasurableSpace GI := specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AKI_borel : BorelSpace GI := specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AKI_links (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint
variable (H : ℕ)
local notation "CfgI" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muI" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "PhysI" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "fI" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "fcI" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "VI" => p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "pI" => p4Q2PZ37AFZ_plaquetteCount H
local notation "WI" => periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "KI" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel H 2
local notation "TI" => decomposableOneSliceTransferIntegral H 2
local notation "PI" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "SI" => periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "psiI" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector H 2 (by norm_num)
local notation "ZI" => p4Q2PZ37AIF_originalCrossingPartition H
local notation "rI" => p4Q2PZ37ABN_originalTemporalWilsonCoefficient
local notation "uI" => p4Q2PZ37AIW_originalNormalizedSourceTransfer H
local notation "mI" => p4Q2PZ37AIW_originalNormalizedNegativeMargin H
local notation "beta0" => p4Q2PZ37ADC_fixedCoupling

local instance p4Q2PZ37AKI_probability : IsProbabilityMeasure muI := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- Auxiliary coefficient from the actual original crossing eigenlaw. -/
def p4Q2PZ37AKI_originalAffineCoefficient (beta : ℝ) : ℝ :=
  ZI beta * Real.exp (-(beta * pI)) * (rI beta) ^ 4

/-- A new bound, not a replacement source or AJA certificate. -/
def p4Q2PZ37AKI_originalWardTopFloor (beta : ℝ) : ℝ :=
  beta * Real.exp (-(3 * beta * pI)) * VI

/-- The enlarged H-dependent no-witness cutoff. -/
def p4Q2PZ37AKI_logarithmicNoWitnessCutoff : ℝ := Real.log 2 / (2 * pI)

local notation "cI" => p4Q2PZ37AKI_originalAffineCoefficient H
local notation "dI" => p4Q2PZ37AKI_originalWardTopFloor H
local notation "kappaI" => p4Q2PZ37AKI_logarithmicNoWitnessCutoff H

/-- Global affine upper bound at every positive coupling. The right side
need not be pointwise negative; no all-boundary negative premise is used. -/
theorem p4Q2PZ37AKI_originalTransfer_affineUpper
    (beta : ℝ) (hbeta : 0 < beta) (B : CfgI) :
    TI beta fI B ≤ cI beta * fcI B - dI beta := by
  let e : ℝ := Real.exp (-(beta * (pI / 2)))
  let q : ℝ := Real.exp (-(beta * pI))
  let w : ℝ := Real.exp (-(beta / 2) * WI B)
  let M : ℝ := ∫ A : CfgI, KI beta A B * (fcI A) ^ 2 ∂muI
  have he : 0 < e := Real.exp_pos _
  have hq : 0 < q := Real.exp_pos _
  have hw : 0 < w := Real.exp_pos _
  have hZ : 0 < ZI beta := p4Q2PZ37AIF_originalCrossingPartition_pos H beta
  have hV : 0 < VI := (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hp : 0 < pI := p4Q2PZ37AHN_count_pos H
  have he2 : e * e = q := by
    dsimp [e, q]
    rw [← Real.exp_add]
    congr 1
    ring
  have hq3 : q * q * q = Real.exp (-(3 * beta * pI)) := by
    dsimp [q]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hwe : w * e = q * Real.exp (-(beta * fcI B)) := by
    dsimp [w, e, q]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [p4Q2PZ37AGN_originalCenteredContinuous_eq H B]
    ring
  have hW : WI B ≤ 2 * pI :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_le_two_mul_length
      H 2 (by norm_num) B
  have hqw : q ≤ w := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hW hbeta.le
    nlinarith only [h]
  have hM : q * VI ≤ M := p4Q2PZ37AIS_originalCrossingSecondMoment_wardLower H beta B
  have hScalar := p4Q2PZ37AIE_real_centeredLaplace_quadraticUpper
    beta (pI / 2) (fcI B) hbeta.le (by positivity)
    (p4Q2PZ37AGN_originalContinuousSource_abs_le_halfCount H B)
  have hCorr : 0 ≤ (beta * e) * (fcI B) ^ 2 := by positivity
  have hScalar' : fcI B * Real.exp (-(beta * fcI B)) ≤ fcI B := by
    change 0 ≤ (beta * Real.exp (-(beta * (pI / 2)))) * (fcI B) ^ 2 at hCorr
    nlinarith only [hScalar, hCorr]
  have hFirst : w * e * (ZI beta * (rI beta) ^ 4 * fcI B) ≤ cI beta * fcI B := by
    rw [hwe]
    calc
      _ = cI beta * (fcI B * Real.exp (-(beta * fcI B))) := by
        dsimp [p4Q2PZ37AKI_originalAffineCoefficient, q]
        ring
      _ ≤ cI beta * fcI B := mul_le_mul_of_nonneg_left hScalar' (by
        dsimp [p4Q2PZ37AKI_originalAffineCoefficient]
        positivity)
  have hWM : q * (q * VI) ≤ w * M :=
    mul_le_mul hqw hM (mul_nonneg hq.le hV.le) hw.le
  have hSecond : dI beta ≤ w * e * (beta * e * M) := by
    calc
      dI beta = (beta * q) * (q * (q * VI)) := by
        unfold p4Q2PZ37AKI_originalWardTopFloor
        rw [← hq3]
        ring
      _ ≤ (beta * q) * (w * M) :=
        mul_le_mul_of_nonneg_left hWM (mul_nonneg hbeta.le hq.le)
      _ = w * e * (beta * e * M) := by
        calc
          _ = beta * w * (e * e) * M := by rw [he2]; ring
          _ = _ := by ring
  have hUpper := p4Q2PZ37AIN_originalRightWeightedTransfer_quadraticUpper H beta hbeta.le B
  have hCancel : w * Real.exp ((beta / 2) * WI B) = 1 := by
    dsimp [w]
    rw [← Real.exp_add]
    convert Real.exp_zero using 1; ring
  calc
    TI beta fI B = w * (Real.exp ((beta / 2) * WI B) * TI beta fI B) := by
      rw [← mul_assoc, hCancel, one_mul]
    _ ≤ w * (e * (ZI beta * (rI beta) ^ 4 * fcI B - (beta * e) * M)) :=
      mul_le_mul_of_nonneg_left hUpper hw.le
    _ = w * e * (ZI beta * (rI beta) ^ 4 * fcI B) - w * e * (beta * e * M) := by ring
    _ ≤ cI beta * fcI B - dI beta := sub_le_sub hFirst hSecond

/-- The affine coefficient is at most the ACTUAL top norm, by ABN's
original coefficient bound and AIW's unchanged spatial-mean norm floor. -/
theorem p4Q2PZ37AKI_originalAffineCoefficient_bounds
    (beta : ℝ) (hbeta : 0 < beta) :
    0 ≤ cI beta ∧ cI beta ≤ ‖PI beta hbeta.le‖ := by
  have hZ := p4Q2PZ37AIF_originalCrossingPartition_pos H beta
  have hr := p4Q2PZ37ABN_originalTemporalWilsonCoefficient_pos beta hbeta
  have hr1 := p4Q2PZ37ABN_originalTemporalWilsonCoefficient_le_one beta
  have hr4 : (rI beta) ^ 4 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hr.le hr1 4
  constructor
  · unfold p4Q2PZ37AKI_originalAffineCoefficient
    positivity
  · calc
      cI beta ≤ (ZI beta * Real.exp (-(beta * pI))) * 1 :=
        mul_le_mul_of_nonneg_left hr4 (mul_nonneg hZ.le (Real.exp_pos _).le)
      _ = Real.exp (-(beta * pI)) * ZI beta := by ring
      _ ≤ ‖PI beta hbeta.le‖ := p4Q2PZ37AIW_originalPhysicalTransfer_norm_ge_spatialMean H beta hbeta.le

/-- An unconditional negative overlap with one genuine top direction for
ALL beta>0. The source itself is not replaced by its orthogonal projection. -/
theorem p4Q2PZ37AKI_originalSource_top_overlap_allPositive
    (beta : ℝ) (hbeta : 0 < beta) :
    inner ℝ fI (psiI beta hbeta.le) ≤ -(dI beta) := by
  let P : PhysI →L[ℝ] PhysI := PI beta hbeta.le
  let psi : PhysI := psiI beta hbeta.le
  let g : Lp ℝ 2 muI := psi
  let c : ℝ := cI beta
  let d : ℝ := dI beta
  let I : ℝ := ∫ A : CfgI, g A ∂muI
  let F : ℝ := inner ℝ fI psi
  have hV : 0 < VI := (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hd : 0 < d := by dsimp [d, p4Q2PZ37AKI_originalWardTopFloor]; positivity
  have hNorm : 0 < ‖P‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) beta hbeta.le
  have hCoeff : 0 ≤ c ∧ c ≤ ‖P‖ := p4Q2PZ37AKI_originalAffineCoefficient_bounds H beta hbeta
  have hg : ∀ᵐ A ∂muI, 0 ≤ g A :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_ae_nonnegative
      H 2 (by norm_num) beta hbeta.le
  have hSource : (fun A : CfgI => (fI : Lp ℝ 2 muI) A) =ᵐ[muI] fcI := by
    rw [p4Q2PZ37AFZ_originalCenteredSource_eq_toLp]
    exact ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := (2 : ENNReal)) (μ := muI) fcI
  have hRaw : ∀ᵐ A ∂muI,
      (((P fI : PhysI) : Lp ℝ 2 muI) - c • (fI : Lp ℝ 2 muI)) A ≤ -d := by
    filter_upwards [Lp.coeFn_sub ((P fI : PhysI) : Lp ℝ 2 muI) (c • (fI : Lp ℝ 2 muI)),
      Lp.coeFn_smul c (fI : Lp ℝ 2 muI),
      p4Q2PZ37AIW_originalPhysicalTransfer_coeFn H beta hbeta.le fI, hSource]
      with A hSub hSmul hPA hfA
    simp only [Pi.sub_apply] at hSub
    simp only [Pi.smul_apply, smul_eq_mul] at hSmul
    rw [hSub, hSmul, hPA, hfA]
    have h := p4Q2PZ37AKI_originalTransfer_affineUpper H beta hbeta A
    change TI beta fI A - c * fcI A ≤ -d
    linarith only [h]
  have hPair := realL2_inner_le_neg_floor_mul_mass_akg muI
    (((P fI : PhysI) : Lp ℝ 2 muI) - c • (fI : Lp ℝ 2 muI)) g d hRaw hg
  change inner ℝ (P fI - c • fI) psi ≤ -d * I at hPair
  rw [inner_sub_left (𝕜 := ℝ) (P fI : PhysI) (c • fI) psi,
    real_inner_smul_left (fI : PhysI) psi c] at hPair
  have hSymm : (P : PhysI →ₗ[ℝ] PhysI).IsSymmetric :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_isSymmetric
      H 2 (by norm_num) beta hbeta.le
  have hEigen : P psi = ‖P‖ • psi :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_eigen
      H 2 (by norm_num) beta hbeta.le
  have hEq : inner ℝ (P fI) psi = ‖P‖ * F := by
    calc
      inner ℝ (P fI) psi = inner ℝ fI (P psi) := hSymm fI psi
      _ = ‖P‖ * F := by
        rw [hEigen]
        exact real_inner_smul_right (fI : PhysI) psi ‖P‖
  rw [hEq] at hPair
  have hMass : ‖P‖ ≤ I := p4Q2PZ37AKG_originalNonnegativeTop_mass_ge_norm H beta hbeta.le
  have hdI : 0 < d * I := mul_pos hd (hNorm.trans_le hMass)
  have hFneg : F < 0 := by
    by_contra hNot
    have hF0 : 0 ≤ F := le_of_not_gt hNot
    have hNonneg : 0 ≤ (‖P‖ - c) * F := mul_nonneg (sub_nonneg.mpr hCoeff.2) hF0
    nlinarith only [hPair, hNonneg, hdI]
  have hcF : c * F ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hCoeff.1 hFneg.le
  have hdMass : d * ‖P‖ ≤ d * I := mul_le_mul_of_nonneg_left hMass hd.le
  have hBound : ‖P‖ * F ≤ ‖P‖ * (-d) := by nlinarith only [hPair, hcF, hdMass]
  change F ≤ -d
  by_contra hNot
  have hGt : -d < F := lt_of_not_ge hNot
  exact (not_lt_of_ge hBound) (mul_lt_mul_of_pos_left hGt hNorm)

/-- All-coupling power lower bound from the SAME original top overlap.
This is finite-H and beta-dependent; it is not uniform coercivity. -/
theorem p4Q2PZ37AKI_originalAllPowers_energy_ge_wardFloor_sq
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ) :
    (dI beta) ^ 2 ≤ ‖((SI beta hbeta.le) ^ n) fI‖ ^ 2 := by
  let P : PhysI →L[ℝ] PhysI := PI beta hbeta.le
  let S : PhysI →L[ℝ] PhysI := SI beta hbeta.le
  let psi : PhysI := psiI beta hbeta.le
  have hNorm : 0 < ‖P‖ := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
    H 2 (by norm_num) beta hbeta.le
  have hUnit : ‖psi‖ = 1 := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_norm
    H 2 (by norm_num) beta hbeta.le
  have hEigen : P psi = ‖P‖ • psi := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_eigen
    H 2 (by norm_num) beta hbeta.le
  have hFix : S psi = psi := by
    change ‖P‖⁻¹ • P psi = psi
    rw [hEigen, smul_smul, inv_mul_cancel₀ hNorm.ne', one_smul]
  have hSymm : (S : PhysI →ₗ[ℝ] PhysI).IsSymmetric :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H 2 (by norm_num) beta hbeta.le
  have hV : 0 < VI := (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hd : 0 ≤ dI beta := by unfold p4Q2PZ37AKI_originalWardTopFloor; positivity
  exact realHilbert_fixedUnit_power_normSq_ge_neg_overlap_akg S hSymm psi hUnit hFix fI
    (dI beta) hd (p4Q2PZ37AKI_originalSource_top_overlap_allPositive H beta hbeta) n

/-- AJA upper envelope uses only the unchanged margin and Haar probability;
it does not assert that the original negative region is the whole space. -/
theorem p4Q2PZ37AKI_originalAJA_le_normalizedVarianceEnvelope_sq
    (beta : ℝ) (hbeta : 0 < beta) :
    (mI beta hbeta.le) ^ 2 *
      Measure.real muI {A : CfgI | uI beta hbeta.le A < -(mI beta hbeta.le)} ≤
        (beta * Real.exp (-(beta * pI)) * VI / 2) ^ 2 := by
  let R : Set CfgI := {A | uI beta hbeta.le A < -(mI beta hbeta.le)}
  have hMass : Measure.real muI R ≤ 1 := by
    have h := ENNReal.toReal_mono (measure_ne_top muI Set.univ)
      (measure_mono (Set.subset_univ R))
    simpa only [Measure.real, measure_univ, ENNReal.toReal_one] using h
  have hm0 := (p4Q2PZ37AIW_originalNormalizedNegativeMargin_pos H beta hbeta).le
  have hm := (p4Q2PZ37AIW_originalNormalizedNegativeMargin_bounds H beta hbeta.le).2
  calc
    _ ≤ (mI beta hbeta.le) ^ 2 * 1 := mul_le_mul_of_nonneg_left hMass (sq_nonneg _)
    _ = (mI beta hbeta.le) ^ 2 := mul_one _
    _ ≤ _ := pow_le_pow_left₀ hm0 hm 2

/-- New logarithmic interval, including its endpoint. The energy may equal
B at this coarse comparison boundary; that still excludes a STRICT witness. -/
theorem p4Q2PZ37AKI_originalLog_no_AJA_power_witness
    (beta : ℝ) (hbeta : 0 < beta) (hLog : beta ≤ kappaI) :
    ¬ ∃ n : ℕ, ‖((SI beta hbeta.le) ^ n) fI‖ ^ 2 <
      (mI beta hbeta.le) ^ 2 *
        Measure.real muI {A : CfgI | uI beta hbeta.le A < -(mI beta hbeta.le)} := by
  have hp := p4Q2PZ37AHN_count_pos H
  have hV : 0 < VI := (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hScale : beta * (2 * pI) ≤ Real.log 2 :=
    (le_div_iff₀ (by positivity : 0 < 2 * pI)).mp hLog
  have hExp : (1 / 2 : ℝ) ≤ Real.exp (-(2 * beta * pI)) := by
    calc
      (1 / 2 : ℝ) = Real.exp (-(Real.log 2)) := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        norm_num
      _ ≤ Real.exp (-(2 * beta * pI)) := Real.exp_le_exp.mpr (by nlinarith only [hScale])
  have hFactor : Real.exp (-(beta * pI)) * Real.exp (-(2 * beta * pI)) =
      Real.exp (-(3 * beta * pI)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hEnvelope : beta * Real.exp (-(beta * pI)) * VI / 2 ≤ dI beta := by
    calc
      _ = (beta * Real.exp (-(beta * pI)) * VI) * (1 / 2) := by ring
      _ ≤ (beta * Real.exp (-(beta * pI)) * VI) * Real.exp (-(2 * beta * pI)) :=
        mul_le_mul_of_nonneg_left hExp (by positivity)
      _ = beta * (Real.exp (-(beta * pI)) * Real.exp (-(2 * beta * pI))) * VI := by ring
      _ = dI beta := by rw [hFactor]; rfl
  have hBudget := p4Q2PZ37AKI_originalAJA_le_normalizedVarianceEnvelope_sq H beta hbeta
  have hSq := pow_le_pow_left₀ (by positivity : 0 ≤ beta * Real.exp (-(beta * pI)) * VI / 2) hEnvelope 2
  rintro ⟨n, hn⟩
  exact (not_lt_of_ge ((hBudget.trans hSq).trans
    (p4Q2PZ37AKI_originalAllPowers_energy_ge_wardFloor_sq H beta hbeta n))) hn

/-- This is a strict extension beyond the already certified AIM interval. -/
theorem p4Q2PZ37AKI_oldCubicCutoff_lt_logarithmic :
    p4Q2PZ37AIM_elementaryCubicSmallCoupling H < kappaI := by
  have hp := p4Q2PZ37AHN_count_pos H
  have hu := p4Q2PZ37AIM_identityHaarRoot_le_one H
  have hLog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    linarith only [h]
  calc
    p4Q2PZ37AIM_elementaryCubicSmallCoupling H ≤ 1 / (16 * pI + 1) :=
      div_le_div_of_nonneg_right hu (by positivity)
    _ < 1 / (4 * pI) := (div_lt_div_iff₀ (by positivity) (by positivity)).mpr (by nlinarith only [hp])
    _ = (1 / 2 : ℝ) / (2 * pI) := by ring
    _ ≤ kappaI := div_le_div_of_nonneg_right hLog (by positivity)

/-- At the ORIGINAL minimal volume H=0, even beta0 lies in the newly
certified interval. This is not a statement about beta0 at every volume. -/
theorem p4Q2PZ37AKI_fixedCoupling_lt_logarithmic_at_zero :
    beta0 < p4Q2PZ37AKI_logarithmicNoWitnessCutoff 0 := by
  have hLog : Real.log (3 / 2 : ℝ) < Real.log 2 := Real.log_lt_log (by norm_num) (by norm_num)
  have hPos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  unfold p4Q2PZ37AKI_logarithmicNoWitnessCutoff
  rw [p4Q2PZ37AIB_plaquetteCount_exact]
  change Real.log (3 / 2 : ℝ) / 64 < Real.log 2 / (2 * (24 * (((0 : ℕ) : ℝ) + 1) ^ 3))
  norm_num
  linarith only [hLog, hPos]

/-- Actual fixed beta0, actual H=0, actual original AJA budget: no witness. -/
theorem p4Q2PZ37AKI_originalFixedCoupling_zero_no_AJA_power_witness :
    ¬ ∃ n : ℕ,
      ‖((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        0 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le) ^ n)
          (p4Q2PZ37ZW_originalCenteredPhysicalDirection 0)‖ ^ 2 <
        (p4Q2PZ37AIW_originalNormalizedNegativeMargin 0 beta0 p4Q2PZ37ADC_fixedCoupling_pos.le) ^ 2 *
          Measure.real (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure 0 2)
            {A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration 0 2 |
              p4Q2PZ37AIW_originalNormalizedSourceTransfer 0 beta0 p4Q2PZ37ADC_fixedCoupling_pos.le A <
                -(p4Q2PZ37AIW_originalNormalizedNegativeMargin 0 beta0 p4Q2PZ37ADC_fixedCoupling_pos.le)} :=
  p4Q2PZ37AKI_originalLog_no_AJA_power_witness 0 beta0 p4Q2PZ37ADC_fixedCoupling_pos
    p4Q2PZ37AKI_fixedCoupling_lt_logarithmic_at_zero.le

/-- Necessary location, not existence, beyond the logarithmic cutoff. -/
theorem p4Q2PZ37AKI_originalAJA_witness_requires_above_logarithmic
    (beta : ℝ) (hbeta : 0 < beta)
    (hWitness : ∃ n : ℕ, ‖((SI beta hbeta.le) ^ n) fI‖ ^ 2 <
      (mI beta hbeta.le) ^ 2 *
        Measure.real muI {A : CfgI | uI beta hbeta.le A < -(mI beta hbeta.le)}) :
    kappaI < beta := by
  by_contra hNot
  exact p4Q2PZ37AKI_originalLog_no_AJA_power_witness H beta hbeta (le_of_not_gt hNot) hWitness

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

/-! Thirteen named declarations with independent axiom audits. -/
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKI_originalAffineCoefficient
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKI_originalWardTopFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKI_logarithmicNoWitnessCutoff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKI_originalTransfer_affineUpper
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKI_originalAffineCoefficient_bounds
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKI_originalSource_top_overlap_allPositive
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKI_originalAllPowers_energy_ge_wardFloor_sq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKI_originalAJA_le_normalizedVarianceEnvelope_sq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKI_originalLog_no_AJA_power_witness
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKI_oldCubicCutoff_lt_logarithmic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKI_fixedCoupling_lt_logarithmic_at_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKI_originalFixedCoupling_zero_no_AJA_power_witness
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKI_originalAJA_witness_requires_above_logarithmic
