import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalWeightedDefectQuantitativeV5_PZ37AJS
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AJT — exact original weighted-to-physical-L² defect bridge

AJS proved a strictly positive integral of the GENUINE one-slab
original centered ZW source difference against the original positive
right spatial Wilson halfweight. Here, by an actual almost-everywhere
representative identification, this scalar is shown to be the REAL
Hilbert L² pairing of (f0 - S f0) with the genuine Wilson halfweight.

The exact original right weight has pointwise upper bound exp(beta*pH),
which controls its genuine probability-Haar L² norm. Cauchy-Schwarz
gives a physical, strictly positive defect NORM lower bound.

AIK's ALREADY CERTIFIED rational sphere fraction 1/384 to power
4*card(Link) is used, not a guessed numerical Haar mass.

AJA strict budget and finite witness remain separate numerical
questions. No unconditional AJA witness or continuum gap is asserted.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "GT" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AJT_group : IsTopologicalGroup GT :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AJT_compact : CompactSpace GT :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AJT_secondCountable : SecondCountableTopology GT :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AJT_measurable : MeasurableSpace GT :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AJT_borel : BorelSpace GT :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AJT_linkFintype (K : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink K) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "PhysT" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "CfgT" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muT" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "fT" =>
  p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "fcT" =>
  p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "WT" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "pT" =>
  p4Q2PZ37AFZ_plaquetteCount H
local notation "VT" =>
  p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "PT" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "ST" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "RT" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator H 2 (by norm_num)
local notation "TT" => decomposableOneSliceTransferIntegral H 2
local notation "vT" => p4Q2PZ37AIK_elementarySourceVarianceFloor H
local notation "DwT" => p4Q2PZ37AJS_originalWeightedOneStepDefectIntegral H

local instance p4Q2PZ37AJT_probability : IsProbabilityMeasure muT := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- The exact right spatial Wilson halfweight, as an ORIGINAL continuous
function on the actual spatial link-configuration compact space. -/
def p4Q2PZ37AJT_originalRightHalfweightContinuous
    (beta : ℝ) : CfgT →��� ℝ :=
  ⟨(fun B : CfgT => Real.exp ((beta / 2) * WT B)),
    Real.continuous_exp.comp
      (continuous_const.mul
        (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2))⟩

/-- Genuine Haar L² representative of the SAME original halfweight. -/
def p4Q2PZ37AJT_originalRightHalfweightL2
    (beta : ℝ) : Lp ℝ 2 muT :=
  ContinuousMap.toLp (E := ℝ) 2 muT ℝ
    (p4Q2PZ37AJT_originalRightHalfweightContinuous H beta)

theorem p4Q2PZ37AJT_originalRightHalfweightL2_ae
    (beta : ℝ) :
    (fun B : CfgT => p4Q2PZ37AJT_originalRightHalfweightL2 H beta B)
      =ᵐ[muT] (fun B : CfgT => Real.exp ((beta / 2) * WT B)) := by
  change
    (fun B : CfgT =>
      (ContinuousMap.toLp (E := ℝ) 2 muT ℝ
        (p4Q2PZ37AJT_originalRightHalfweightContinuous H beta)) B)
       =ᵐ[muT] (fun B : CfgT =>
        (p4Q2PZ37AJT_originalRightHalfweightContinuous H beta) B)
  exact ContinuousMap.coeFn_toLp
    (𝕜 := ℝ) (p := (2 : ENNReal)) (μ := muT)
    (p4Q2PZ37AJT_originalRightHalfweightContinuous H beta)

/-- Verified pointwise AIG weight cap transfers to the actual
normalised product-Haar L² weight norm. -/
theorem p4Q2PZ37AJT_originalRightHalfweightL2_norm_le
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖p4Q2PZ37AJT_originalRightHalfweightL2 H beta‖ ≤
      Real.exp (beta * pT) := by
  let w : Lp ℝ 2 muT := p4Q2PZ37AJT_originalRightHalfweightL2 H beta
  have hRep := p4Q2PZ37AJT_originalRightHalfweightL2_ae H beta
  have hBound : ∀ᵐ B ∂muT, ‖w B‖ ≤ Real.exp (beta * pT) := by
    filter_upwards [hRep] with B hB
    rw [hB, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact p4Q2PZ37AIG_originalRightWeight_le_expCount H beta hbeta B
  have h :=
    Lp.norm_le_of_ae_bound (f := w) (Real.exp_pos _).le hBound
  simpa only [measureUnivNNReal, measure_univ, ENNReal.toNNReal_one,
    NNReal.coe_one, one_rpow, one_mul] using h

/-- Original true physical L² source-minus-normalized-transfer and its
continuous Haar representative are almost everywhere the SAME object.
This is not pointwise evaluation of an arbitrary L² equivalence class. -/
theorem p4Q2PZ37AJT_originalOneStepDefect_ae
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    (fun B : CfgT =>
      (((fT - ST beta hbeta fT : PhysT) : Lp ℝ 2 muT) B)) =ᵐ[muT]
    (fun B : CfgT =>
      fcT B - ‖PT beta hbeta‖⁻¹ * TT beta fT B) := by
  have hSource :
      (fun B : CfgT => (fT : Lp ℝ 2 muT) B) =ᵐ[muT] fcT := by
    rw [p4Q2PZ37AFZ_originalCenteredSource_eq_toLp]
    exact ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := (2 : ENNReal))
      (μ := muT) fcT
  have hTransfer :=
    p4Q2PZ37AIW_originalNormalizedSourceTransfer_coeFn
      H beta hbeta
  have hTransfer' :
      (fun B : CfgT =>
        (((ST beta hbeta fT : PhysT) : Lp ℝ 2 muT) B)) =ᵐ[muT]
      (fun B : CfgT => ‖PT beta hbeta‖⁻¹ * TT beta fT B) := by
    filter_upwards [hTransfer] with B hB
    change
      ((ST beta hbeta fT : PhysT) : Lp ℝ 2 muT) B =
        TT beta fT B / ‖PT beta hbeta‖ at hB
    rw [hB, div_eq_mul_inv, mul_comm]
  change
    (fun B : CfgT =>
      (((fT : Lp ℝ 2 muT) -
        ((ST beta hbeta fT : PhysT) : Lp ℝ 2 muT)) B)) =ᵐ[muT]
    (fun B : CfgT =>
      fcT B - ‖PT beta hbeta‖⁻¹ * TT beta fT B)
  filter_upwards
    [Lp.coeFn_sub (fT : Lp ℝ 2 muT)
      ((ST beta hbeta fT : PhysT) : Lp ℝ 2 muT),
      hSource, hTransfer'] with B hSub hSrc hT
  rw [hSub, hSrc, hT]

/-- AJS genuine weighted integral is the exact scalar product in
the true original physical-Haar L² carrier, not a surrogate norm. -/
theorem p4Q2PZ37AJT_originalWeightedDefect_eq_realL2_inner
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    DwT beta hbeta =
      inner ℝ
        (p4Q2PZ37AJT_originalRightHalfweightL2 H beta)
        (((fT - ST beta hbeta fT : PhysT) : Lp ℝ 2 muT)) := by
  let w := p4Q2PZ37AJT_originalRightHalfweightL2 H beta
  have hw := p4Q2PZ37AJT_originalRightHalfweightL2_ae H beta
  have hd := p4Q2PZ37AJT_originalOneStepDefect_ae H beta hbeta
  change DwT beta hbeta =
    inner ℝ w (((fT - ST beta hbeta fT : PhysT) : Lp ℝ 2 muT))
  rw [MeasureTheory.L2.inner_def]
  unfold p4Q2PZ37AJS_originalWeightedOneStepDefectIntegral
  apply integral_congr_ae
  filter_upwards [hw, hd] with B hWB hDB
  rw [hWB, hDB]
  simp only [real_inner_eq_re_inner (𝕜 := ℝ),
    RCLike.inner_apply, RCLike.re_to_real, conj_trivial]

/-- Duality bridge: the genuine AJS weighted deficit cannot exceed the
physical Haar-L² one-step defect times the ACTUAL halfweight norm. -/
theorem p4Q2PZ37AJT_originalWeightedDefect_le_exp_mul_physicalDefect
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    DwT beta hbeta ≤
      Real.exp (beta * pT) * ‖fT - ST beta hbeta fT‖ := by
  let w := p4Q2PZ37AJT_originalRightHalfweightL2 H beta
  let d : Lp ℝ 2 muT :=
    ((fT - ST beta hbeta fT : PhysT) : Lp ℝ 2 muT)
  have heq := p4Q2PZ37AJT_originalWeightedDefect_eq_realL2_inner
    H beta hbeta
  change DwT beta hbeta = inner ℝ w d at heq
  have hCS : inner ℝ w d ≤ ‖w‖ * ‖d‖ := real_inner_le_norm w d
  have hw : ‖w‖ ≤ Real.exp (beta * pT) :=
    p4Q2PZ37AJT_originalRightHalfweightL2_norm_le H beta hbeta
  have hbound :
      inner ℝ w d ≤ Real.exp (beta * pT) * ‖d‖ :=
    hCS.trans (mul_le_mul_of_nonneg_right hw (norm_nonneg d))
  rw [heq]
  exact hbound

/-- Positive, explicit true PHYSICAL L² one-step norm floor from AJS,
AIG and AJQ. Numerator still retains actual original Haar variance. -/
theorem p4Q2PZ37AJT_originalPhysicalDefect_ge_explicitVariance
    (beta : ℝ) (hbeta : 0 < beta) :
    beta * VT / Real.exp (beta * pT) ≤
      ‖fT - ST beta hbeta.le fT‖ := by
  let P := PT beta hbeta.le
  have hAJS := p4Q2PZ37AJS_originalWeightedDefect_ge_explicitTwoSide
    H beta hbeta
  have hZ : 0 < p4Q2PZ37AIF_originalCrossingPartition H beta :=
    p4Q2PZ37AIF_originalCrossingPartition_pos H beta
  have hV : 0 < VT := (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hTerm :
      0 ≤ ‖P‖⁻¹ *
        (beta * p4Q2PZ37AIF_originalCrossingPartition H beta *
          Real.exp (-(beta * pT)) * VT) := by
    apply mul_nonneg (inv_nonneg.mpr (norm_nonneg P))
    exact (mul_pos
      (mul_pos (mul_pos hbeta hZ) (Real.exp_pos _)) hV).le
  have hLower :
      beta * VT ≤ DwT beta hbeta.le := by
    change beta * VT +
      ‖P‖⁻¹ *
        (beta * p4Q2PZ37AIF_originalCrossingPartition H beta *
          Real.exp (-(beta * pT)) * VT) ≤ DwT beta hbeta.le at hAJS
    linarith only [hAJS, hTerm]
  have hUpper :=
    p4Q2PZ37AJT_originalWeightedDefect_le_exp_mul_physicalDefect
      H beta hbeta.le
  exact (div_le_iff₀ (Real.exp_pos _)).2 (hLower.trans hUpper)

/-- Explicit RATIONAL finite-power source witness v_H =
(3*p_H/8)^2 (1/384)^(4*n_H), inherited without alteration from AIK.
This is a true physical-Haar L² defect norm lower bound. -/
theorem p4Q2PZ37AJT_originalPhysicalDefect_ge_rationalVarianceFloor
    (beta : ℝ) (hbeta : 0 < beta) :
    beta * vT / Real.exp (beta * pT) ≤
      ‖fT - ST beta hbeta.le fT‖ := by
  have hV := p4Q2PZ37AIK_elementarySourceVarianceFloor_le_original H
  have hDef := p4Q2PZ37AJT_originalPhysicalDefect_ge_explicitVariance
    H beta hbeta
  exact (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hV hbeta.le)
    (Real.exp_pos _).le).trans hDef

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

/-! The ten newly declared statements are separately kernel-axiom audited. -/
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJT_originalRightHalfweightContinuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJT_originalRightHalfweightL2
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJT_originalRightHalfweightL2_ae
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJT_originalRightHalfweightL2_norm_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJT_originalOneStepDefect_ae
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJT_originalWeightedDefect_eq_realL2_inner
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJT_originalWeightedDefect_le_exp_mul_physicalDefect
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJT_originalPhysicalDefect_ge_explicitVariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJT_originalPhysicalDefect_ge_rationalVarianceFloor
