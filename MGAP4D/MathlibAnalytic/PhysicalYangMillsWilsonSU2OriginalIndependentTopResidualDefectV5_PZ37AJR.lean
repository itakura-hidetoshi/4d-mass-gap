import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalReverseLaplaceTopExcitationV5_PZ37AJQ
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AJR — independent one-step bound for the original extra-top residual

This leaf uses AJQ's unconditionally certified original-source nonfixedness
and the ORIGINAL AJA/AJF Wilson and SU(2) Haar data. Unlike AJP's two-power
posterior limit, it extracts a strict variance deficit from the genuine
single-step normalized transfer defect f₀ - S f₀.

Write V_H = ∫ f₀² dμ_H, α=⟨f₀,Ω⟩, r=Qf₀-αΩ and
q=‖R‖<1, where F=ker(S-I), Q projects onto the COMPLETE top space, and
R is the already existing exact restriction to its complement.

The exact original Haar variance V_H=‖f₀‖² and the one-step bound imply

  α² + ‖r‖² + (‖f₀-Sf₀‖/(1+q))² ≤ V_H.

AJQ ensures ‖f₀-Sf₀‖>0, so α²+‖r‖²<V_H without any rank-one
top assumption or AJA strict-budget premise.

The defect norm is an original physical Wilson quantity, not a fabricated
numerical constant. This is an INDEPENDENT quantitative expression but
is NOT itself a numerical AJA finite-power witness, nor a statement that
the transferred orthogonal component is nonzero, nor any H-uniform gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open Filter
open scoped InnerProductSpace Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- One-step Wilson defect is bounded by the EXACT full-top-orthogonal
source norm times 1+‖R‖, without assuming R is injective or top is a line. -/
theorem realHilbert_fullTop_oneStep_defect_norm_le_ajr
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E)
    [(realHilbertTopEigenspace S).HasOrthogonalProjection]
    (hSymm : (S : E →ₗ[ℝ] E).IsSymmetric)
    (x : E) :
    ‖x - S x‖ ≤
      (1 + ‖realHilbertTopEigenspaceOrthogonalRestriction S hSymm‖) *
        ‖((realHilbertTopEigenspace S)ᗮ).starProjection x‖ := by
  let F := realHilbertTopEigenspace S
  let R := realHilbertTopEigenspaceOrthogonalRestriction S hSymm
  letI : CompleteSpace F := (realHilbertTopEigenspace_isClosed S).completeSpace_coe
  letI : CompleteSpace Fᗮ := F.isClosed_orthogonal.completeSpace_coe
  have hproj :
      ‖x - F.starProjection x‖ = ‖(Fᗮ).starProjection x‖ := by
    rw [F.starProjection_orthogonal_val]
  have hstep :
      ‖S x - F.starProjection x‖ ≤
        ‖R‖ * ‖(Fᗮ).starProjection x‖ := by
    have h :=
      realHilbert_fullTop_power_sub_projection_norm_le_aji
        S hSymm 1 (by norm_num) x
    simpa only [pow_one] using h
  change ‖x - S x‖ ≤ (1 + ‖R‖) * ‖(Fᗮ).starProjection x‖
  calc
    ‖x - S x‖ =
        ‖(x - F.starProjection x) - (S x - F.starProjection x)‖ := by
          congr 1
          abel
    _ ≤ ‖x - F.starProjection x‖ + ‖S x - F.starProjection x‖ :=
        norm_sub_le _ _
    _ ≤ ‖(Fᗮ).starProjection x‖ +
          ‖R‖ * ‖(Fᗮ).starProjection x‖ := by
          rw [hproj]
          exact add_le_add_left hstep _
    _ = (1 + ‖R‖) * ‖(Fᗮ).starProjection x‖ := by ring

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "PhysR" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "CfgR" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muR" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "fR" =>
  p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "OmegaR" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector H 2 (by norm_num)
local notation "SR" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "RR" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator H 2 (by norm_num)
local notation "VR" => p4Q2PZ37AHN_originalSource_HaarSecondMoment H

local instance p4Q2PZ37AJR_physicalComplete (K : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule K 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    K 2).completeSpace_coe

local instance p4Q2PZ37AJR_topComplete
    (K : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
        K 2 (by norm_num) beta hbeta) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_isClosed
    K 2 (by norm_num) beta hbeta).completeSpace_coe

/-- Exact genuine original-source Haar variance equals the physical
Hilbert L² norm squared, not a surrogate projected or normalized source. -/
theorem p4Q2PZ37AJR_originalSource_norm_sq_eq_HaarVariance :
    ‖fR‖ ^ 2 = VR := by
  change ‖(fR : Lp ℝ 2 muR)‖ ^ 2 = VR
  rw [realL2_norm_sq_eq_integral_norm_sq]
  rw [p4Q2PZ37AHN_originalSource_HaarSecondMoment_eq_physical]
  apply integral_congr_ae
  filter_upwards with B
  simp only [Real.norm_eq_abs, sq_abs]

/-- Quantitative independent upper: the true original extra-top residual
plus selected overlap has an explicit strictly positive one-step Wilson
defect contribution to the total original Haar variance. -/
theorem p4Q2PZ37AJR_originalSource_extraTop_oneStep_variance_budget
    (beta : ℝ) (hbeta : 0 < beta) :
    (inner ℝ fR (OmegaR beta hbeta.le)) ^ 2 +
      ‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ^ 2 +
      (‖fR - (SR beta hbeta.le) fR‖ /
        (1 + ‖RR beta hbeta.le‖)) ^ 2 ≤ VR := by
  let S : PhysR →L[ℝ] PhysR := SR beta hbeta.le
  let F : Submodule ℝ PhysR := realHilbertTopEigenspace S
  let hS : (S : PhysR →ₗ[ℝ] PhysR).IsSymmetric :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H 2 (by norm_num) beta hbeta.le
  let R := realHilbertTopEigenspaceOrthogonalRestriction S hS
  letI : CompleteSpace F := (realHilbertTopEigenspace_isClosed S).completeSpace_coe
  letI : CompleteSpace Fᗮ := F.isClosed_orthogonal.completeSpace_coe
  have hOne :
      ‖fR - S fR‖ ≤
        (1 + ‖R‖) * ‖(Fᗮ).starProjection fR‖ :=
    realHilbert_fullTop_oneStep_defect_norm_le_ajr S hS fR
  have hcoef : 0 < 1 + ‖R‖ := by
    have hnonneg : 0 ≤ ‖R‖ := norm_nonneg R
    linarith
  have hDiv :
      ‖fR - S fR‖ / (1 + ‖R‖) ≤
        ‖(Fᗮ).starProjection fR‖ := by
    apply (div_le_iff₀ hcoef).2
    simpa only [mul_comm] using hOne
  have hSq :
      (‖fR - S fR‖ / (1 + ‖R‖)) ^ 2 ≤
        ‖(Fᗮ).starProjection fR‖ ^ 2 := by
    have hd0 : 0 ≤ ‖fR - S fR‖ / (1 + ‖R‖) :=
      div_nonneg (norm_nonneg _) hcoef.le
    have hp0 : 0 ≤ ‖(Fᗮ).starProjection fR‖ := norm_nonneg _
    have hMul := mul_nonneg (sub_nonneg.mpr hDiv) (add_nonneg hd0 hp0)
    nlinarith
  have hFull :
      ‖F.starProjection fR‖ ^ 2 =
        (inner ℝ fR (OmegaR beta hbeta.le)) ^ 2 +
        ‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ^ 2 := by
    change ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 =
      (inner ℝ fR (OmegaR beta hbeta.le)) ^ 2 +
        ‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ^ 2
    exact p4Q2PZ37AJF_originalSourceTop_norm_sq_eq_selected_add_extra H beta hbeta
  have hP := F.norm_sq_eq_add_norm_sq_starProjection fR
  simp only [F.starProjection_orthogonal_val] at hP
  rw [p4Q2PZ37AJR_originalSource_norm_sq_eq_HaarVariance H, hFull] at hP
  change
    (inner ℝ fR (OmegaR beta hbeta.le)) ^ 2 +
      ‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ^ 2 +
      (‖fR - S fR‖ / (1 + ‖R‖)) ^ 2 ≤ VR
  nlinarith [hP, hSq]

/-- Direct independent extra-top square UPPER bound, retaining the
observed original one-step physical Wilson defect as a positive correction. -/
theorem p4Q2PZ37AJR_originalSource_extraTop_sq_le_independent_defect_budget
    (beta : ℝ) (hbeta : 0 < beta) :
    ‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ^ 2 ≤
      VR - (inner ℝ fR (OmegaR beta hbeta.le)) ^ 2 -
        (‖fR - (SR beta hbeta.le) fR‖ /
          (1 + ‖RR beta hbeta.le‖)) ^ 2 := by
  have h := p4Q2PZ37AJR_originalSource_extraTop_oneStep_variance_budget H beta hbeta
  linarith

/-- AJQ's unconditional non-fixedness makes the one-step Wilson defect
strictly positive; the true source has a nonzero orthogonal sector and the
full-top source square is strictly below the original Haar variance. -/
theorem p4Q2PZ37AJR_originalSource_selectedExtraTop_sq_strict_lt_variance
    (beta : ℝ) (hbeta : 0 < beta) :
    (inner ℝ fR (OmegaR beta hbeta.le)) ^ 2 +
      ‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ^ 2 < VR := by
  let S : PhysR →L[ℝ] PhysR := SR beta hbeta.le
  let R := RR beta hbeta.le
  have hNonfix := p4Q2PZ37AJQ_originalSource_not_fixed_all_positive H beta hbeta
  have hNe : fR - S fR ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm hNonfix)
  have hNorm : 0 < ‖fR - S fR‖ := norm_pos_iff.mpr hNe
  have hCoef : 0 < 1 + ‖R‖ := by
    have hn : 0 ≤ ‖R‖ := norm_nonneg R
    linarith
  have hPos : 0 < (‖fR - S fR‖ / (1 + ‖R‖)) ^ 2 :=
    sq_pos_of_pos (div_pos hNorm hCoef)
  have hBudget :=
    p4Q2PZ37AJR_originalSource_extraTop_oneStep_variance_budget H beta hbeta
  change
    (inner ℝ fR (OmegaR beta hbeta.le)) ^ 2 +
      ‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ^ 2 +
      (‖fR - S fR‖ / (1 + ‖R‖)) ^ 2 ≤ VR at hBudget
  linarith

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

/-! Five kernel-audited declarations; every quantitative input is ORIGINAL. -/
#print axioms MGAP4D.MathlibAnalytic.realHilbert_fullTop_oneStep_defect_norm_le_ajr
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJR_originalSource_norm_sq_eq_HaarVariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJR_originalSource_extraTop_oneStep_variance_budget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJR_originalSource_extraTop_sq_le_independent_defect_budget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJR_originalSource_selectedExtraTop_sq_strict_lt_variance
