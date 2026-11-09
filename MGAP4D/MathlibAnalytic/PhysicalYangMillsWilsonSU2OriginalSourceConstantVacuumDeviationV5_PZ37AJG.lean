import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSourceSelectedTopResidualV5_PZ37AJF
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AJG — actual centered ZW source and selected top-vacuum deviation

The exact ORIGINAL centered signed ZW Gauss-law physical L2 source is
defined by subtracting its physical Haar-constant unit direction.
The constant reference is NOT asserted to be a top eigenvector at beta>0.

We prove the true source is orthogonal to the unchanged physical Haar
constant vector and bound its overlap with the ACTUAL selected unit top
eigenvector by the genuine top vector's deviation from that constant.

This gives a quantitative original-source full-top projection upper
BOUND once combined with the AJF extra-top residual, without making
either deviation or extra-top residual vanish. No new physical source,
transfer, probability, assumption, top simplicity, or volume-uniform
gap is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- A centered source paired with any vector equals its pairing with
that vector's orthogonal residual from the constant direction. -/
theorem realHilbert_centered_inner_eq_direction_deviation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f c omega : E) (hcenter : inner ℝ f c = 0) :
    inner ℝ f omega =
      inner ℝ f (omega - (inner ℝ omega c) • c) := by
  rw [inner_sub_right, real_inner_smul_right, hcenter]
  ring

/-- Cauchy-Schwarz on the ACTUAL nonconstant part of a chosen direction. -/
theorem realHilbert_centered_inner_abs_le_direction_deviation_norm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f c omega : E) (hcenter : inner ℝ f c = 0) :
    |inner ℝ f omega| ≤
      ‖f‖ * ‖omega - (inner ℝ omega c) • c‖ := by
  rw [realHilbert_centered_inner_eq_direction_deviation f c omega hcenter]
  exact abs_real_inner_le_norm f
    (omega - (inner ℝ omega c) • c)

/-- The genuine deviation of a UNIT vector from another UNIT reference
has squared norm 1 minus the squared actual real overlap. -/
theorem realHilbert_unitDirection_deviation_norm_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (omega c : E) (homega : ‖omega‖ = 1) (hc : ‖c‖ = 1) :
    ‖omega - (inner ℝ omega c) • c‖ ^ 2 =
      1 - (inner ℝ omega c) ^ 2 := by
  have h :=
    realHilbert_unitDirection_norm_sq_split omega c hc
  rw [homega] at h
  norm_num at h
  linarith

/-- A quantitative REAL Hilbert bound for an ACTUALLY centered source:
the selected unit direction contributes only through its deviation
from the constant unit reference. -/
theorem realHilbert_centered_selected_overlap_sq_le_deviation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f c omega : E) (hcenter : inner ℝ f c = 0)
    (homega : ‖omega‖ = 1) (hc : ‖c‖ = 1) :
    |inner ℝ f omega| ^ 2 ≤
      ‖f‖ ^ 2 * (1 - (inner ℝ omega c) ^ 2) := by
  let v := omega - (inner ℝ omega c) • c
  have hbound : |inner ℝ f omega| ≤ ‖f‖ * ‖v‖ := by
    exact realHilbert_centered_inner_abs_le_direction_deviation_norm
      f c omega hcenter
  have hpos : 0 ≤ ‖f‖ * ‖v‖ := by positivity
  have hsq : |inner ℝ f omega| ^ 2 ≤ (‖f‖ * ‖v‖) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hbound)
      (add_nonneg (abs_nonneg (inner ℝ f omega)) hpos)]
  have hnorm : ‖v‖ ^ 2 = 1 - (inner ℝ omega c) ^ 2 := by
    exact realHilbert_unitDirection_deviation_norm_sq omega c homega hc
  calc
    |inner ℝ f omega| ^ 2 ≤ (‖f‖ * ‖v‖) ^ 2 := hsq
    _ = ‖f‖ ^ 2 * ‖v‖ ^ 2 := by ring
    _ = ‖f‖ ^ 2 * (1 - (inner ℝ omega c) ^ 2) := by rw [hnorm]

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "PhysG" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "CfgG" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muG" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "fG" =>
  p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "cG" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
local notation "OmegaG" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector H 2 (by norm_num)
local notation "uG" =>
  p4Q2PZ37AIW_originalNormalizedSourceTransfer H
local notation "mG" =>
  p4Q2PZ37AIW_originalNormalizedNegativeMargin H

local instance p4Q2PZ37AJG_physicalComplete (K : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule K 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    K 2).completeSpace_coe

local instance p4Q2PZ37AJG_topComplete
    (K : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
        K 2 (by norm_num) beta hbeta) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_isClosed
    K 2 (by norm_num) beta hbeta).completeSpace_coe

/-- CENTERING IS PROVED DIRECTLY FROM THE ORIGINAL ZW DEFINITION
and the actual unit norm of the Haar-constant physical vector. -/
theorem p4Q2PZ37AJG_originalCenteredZWSource_inner_constant_eq_zero :
    inner ℝ fG cG = 0 := by
  let W : PhysG := p4Q2JU_originalSpatialWilsonPhysicalSource H
  let c : PhysG := cG
  have hc : ‖c‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm H 2
  have hself : inner ℝ c c = 1 := by
    rw [real_inner_self_eq_norm_sq, hc]
    norm_num
  have hbase : inner ℝ (W - (inner ℝ W c) • c) c = 0 := by
    have hsub :
        inner ℝ (W - (inner ℝ W c) • c) c =
          inner ℝ W c - inner ℝ ((inner ℝ W c) • c) c :=
      inner_sub_left W ((inner ℝ W c) • c) c
    have hsmul :
        inner ℝ ((inner ℝ W c) • c) c =
          (inner ℝ W c) * inner ℝ c c :=
      real_inner_smul_left c c (inner ℝ W c)
    calc
      inner ℝ (W - (inner ℝ W c) • c) c =
          inner ℝ W c - inner ℝ ((inner ℝ W c) • c) c := hsub
      _ = inner ℝ W c - (inner ℝ W c) * inner ℝ c c :=
        congrArg (fun z : ℝ => inner ℝ W c - z) hsmul
      _ = 0 := by simp only [hself, mul_one, sub_self]
  change inner ℝ
    ((1 / 2 : ℝ) • (W - (inner ℝ W c) • c)) c = 0
  calc
    inner ℝ ((1 / 2 : ℝ) • (W - (inner ℝ W c) • c)) c =
        (1 / 2 : ℝ) * inner ℝ (W - (inner ℝ W c) • c) c :=
          real_inner_smul_left (W - (inner ℝ W c) • c) c (1 / 2 : ℝ)
    _ = 0 := by rw [hbase]; ring

/-- The true source's overlap with the chosen normalized top eigenvector
comes solely from that eigenvector's deviation from the constant source
centering direction; the constant itself is not assumed top. -/
theorem p4Q2PZ37AJG_originalSource_selectedTop_inner_eq_constantDeviation
    (beta : ℝ) (hbeta : 0 < beta) :
    inner ℝ fG (OmegaG beta hbeta.le) =
      inner ℝ fG
        (OmegaG beta hbeta.le -
          (inner ℝ (OmegaG beta hbeta.le) cG) • cG) := by
  exact realHilbert_centered_inner_eq_direction_deviation
    fG cG (OmegaG beta hbeta.le)
    (p4Q2PZ37AJG_originalCenteredZWSource_inner_constant_eq_zero H)

/-- Genuine original-source selected-top inner-product upper bound
in terms of the actual top unit vector's physical Haar-constant deviation. -/
theorem p4Q2PZ37AJG_originalSource_selectedTop_overlap_abs_le_constantDeviation
    (beta : ℝ) (hbeta : 0 < beta) :
    |inner ℝ fG (OmegaG beta hbeta.le)| ≤
      ‖fG‖ *
        ‖OmegaG beta hbeta.le -
          (inner ℝ (OmegaG beta hbeta.le) cG) • cG‖ := by
  exact realHilbert_centered_inner_abs_le_direction_deviation_norm
    fG cG (OmegaG beta hbeta.le)
    (p4Q2PZ37AJG_originalCenteredZWSource_inner_constant_eq_zero H)

/-- Squared REAL source–selected-top overlap is controlled by genuine
physical source norm and actual normalized top-vacuum deviation
from the ORIGINAL unit constant gauge-invariant L2 direction. -/
theorem p4Q2PZ37AJG_originalSource_selectedTop_overlap_sq_le_constantDeviation
    (beta : ℝ) (hbeta : 0 < beta) :
    |inner ℝ fG (OmegaG beta hbeta.le)| ^ 2 ≤
      ‖fG‖ ^ 2 *
        (1 - (inner ℝ (OmegaG beta hbeta.le) cG) ^ 2) := by
  exact realHilbert_centered_selected_overlap_sq_le_deviation
    fG cG (OmegaG beta hbeta.le)
    (p4Q2PZ37AJG_originalCenteredZWSource_inner_constant_eq_zero H)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_norm
      H 2 (by norm_num) beta hbeta.le)
    (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm H 2)

/-- AJF's exact decomposition gives a genuine upper BOUND on the
ENTIRE ORIGINAL-SOURCE full-top projection: the source norm times
selected-vacuum deviation PLUS the independent extra-top norm. -/
theorem p4Q2PZ37AJG_originalFullTop_norm_sq_le_constantDeviation_add_extra
    (beta : ℝ) (hbeta : 0 < beta) :
    ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 ≤
      ‖fG‖ ^ 2 *
        (1 - (inner ℝ (OmegaG beta hbeta.le) cG) ^ 2) +
      ‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ^ 2 := by
  have hsplit :=
    p4Q2PZ37AJF_originalSourceTop_norm_sq_eq_selected_add_extra
      H beta hbeta
  have hbound :=
    p4Q2PZ37AJG_originalSource_selectedTop_overlap_sq_le_constantDeviation
      H beta hbeta
  rw [hsplit]
  have hs :
      (inner ℝ fG (OmegaG beta hbeta.le)) ^ 2 ≤
        ‖fG‖ ^ 2 *
          (1 - (inner ℝ (OmegaG beta hbeta.le) cG) ^ 2) := by
    simpa only [sq_abs] using hbound
  linarith [hs]

/-- The real centered-vacuum deviation bound yields true
nonzero original transfer orthogonal source only IF its two
H,beta-dependent contributions fit under the genuine AJA certificate.
No such strict budget is asserted here. -/
theorem p4Q2PZ37AJG_originalOrthogonal_ne_zero_of_constantDeviation_extra_budget
    (beta : ℝ) (hbeta : 0 < beta)
    (hBudget :
      ‖fG‖ ^ 2 *
          (1 - (inner ℝ (OmegaG beta hbeta.le) cG) ^ 2) +
        ‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ^ 2 <
      (mG beta hbeta.le) ^ 2 *
        Measure.real muG
          {B : CfgG | uG beta hbeta.le B < -(mG beta hbeta.le)}) :
    p4Q2PZ37AJC_originalNormalizedSourceOrthogonalComponent H beta hbeta ≠ 0 := by
  apply p4Q2PZ37AJD_orthogonal_ne_zero_of_originalSourceTop_small H beta hbeta
  exact lt_of_le_of_lt
    (p4Q2PZ37AJG_originalFullTop_norm_sq_le_constantDeviation_add_extra
      H beta hbeta) hBudget

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

/-! All new true-code declarations: actual Lean kernel axiom output. -/
#print axioms MGAP4D.MathlibAnalytic.realHilbert_centered_inner_eq_direction_deviation
#print axioms MGAP4D.MathlibAnalytic.realHilbert_centered_inner_abs_le_direction_deviation_norm
#print axioms MGAP4D.MathlibAnalytic.realHilbert_unitDirection_deviation_norm_sq
#print axioms MGAP4D.MathlibAnalytic.realHilbert_centered_selected_overlap_sq_le_deviation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJG_originalCenteredZWSource_inner_constant_eq_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJG_originalSource_selectedTop_inner_eq_constantDeviation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJG_originalSource_selectedTop_overlap_abs_le_constantDeviation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJG_originalSource_selectedTop_overlap_sq_le_constantDeviation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJG_originalFullTop_norm_sq_le_constantDeviation_add_extra
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJG_originalOrthogonal_ne_zero_of_constantDeviation_extra_budget
