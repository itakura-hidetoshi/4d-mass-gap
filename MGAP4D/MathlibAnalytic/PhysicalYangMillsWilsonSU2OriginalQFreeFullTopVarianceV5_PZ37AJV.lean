import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSecondPowerAJABudgetV5_PZ37AJU
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AJV — q-free original Wilson full-top residual budget

AJT gives the original centered physical ZW source's TRUE one-step
Hilbert-L2 deficit >= d_H(beta) = beta*v_H/exp(beta*p_H), where
the original AIK rational Haar variance floor v_H > 0 is unchanged.
AJR relates this one-step deficit to the actual full-top-orthogonal
source component with coefficient (1 + ||R_H||). Since the original
normalized positive compact Wilson transfer has 0 <= ||R_H|| < 1,
we can bound the coefficient by TWO with NO numerical surrogate for q.

This proves an unconditional finite-H,beta>0 q-FREE square budget:

    ||Q_H f0||^2 + (d_H(beta)/2)^2 <= V_H.

The full-top projection is the original entire fixed eigenspace,
not a chosen top vector and not a rank-one assumption.
Its selected-vacuum and extra-top residual sum inherits the same
strict explicit correction.

AJA budget B_H,beta is the true unchanged margin^2 times ORIGINAL
negative Haar-region mass. The comparison V_H - d_H(beta)^2/4 < B
remains a separate unproved predicate. Under that predicate the
older AJI finite-power equivalence gives existence of SOME finite
power, not a numerical n=2 witness. AJU retains the distinct
conditional literal n=2 test with the TRUE q-dependent correction.
No global coercivity or 4D continuum mass gap is asserted.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open Filter
open scoped InnerProductSpace Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Q-free real-Hilbert one-step deficit inequality.
Given the true symmetric S, genuine full-top fixed eigenspace and its
orthogonal restricted norm <= 1, any lower bound d <= ||x-Sx||
yields the exact geometric floor d^2/4 for loss of top projection. -/
theorem realHilbert_fullTop_qfree_defect_sq_budget_ajv
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E)
    [(realHilbertTopEigenspace S).HasOrthogonalProjection]
    (hSymm : (S : E →ₗ[ℝ] E).IsSymmetric)
    (hR : ‖realHilbertTopEigenspaceOrthogonalRestriction S hSymm‖ ≤ 1)
    (x : E) (d : ℝ) (hd : 0 ≤ d)
    (hdef : d ≤ ‖x - S x‖) :
    ‖(realHilbertTopEigenspace S).starProjection x‖ ^ 2 +
      (d / 2) ^ 2 ≤ ‖x‖ ^ 2 := by
  let F : Submodule ℝ E := realHilbertTopEigenspace S
  let R := realHilbertTopEigenspaceOrthogonalRestriction S hSymm
  let y : ℝ := ‖(Fᗮ).starProjection x‖
  letI : CompleteSpace F := (realHilbertTopEigenspace_isClosed S).completeSpace_coe
  letI : CompleteSpace Fᗮ := F.isClosed_orthogonal.completeSpace_coe
  have hq : ‖R‖ ≤ 1 := hR
  have hq0 : 0 ≤ ‖R‖ := norm_nonneg R
  have hCoef : 1 + ‖R‖ ≤ 2 := by linarith only [hq]
  have hy0 : 0 ≤ y := norm_nonneg _
  have hOne : ‖x - S x‖ ≤ (1 + ‖R‖) * y := by
    have h := realHilbert_fullTop_oneStep_defect_norm_le_ajr S hSymm x
    change ‖x - S x‖ ≤ (1 + ‖R‖) * y at h
    exact h
  have hDouble : d ≤ 2 * y := by
    calc
      d ≤ ‖x - S x‖ := hdef
      _ ≤ (1 + ‖R‖) * y := hOne
      _ ≤ 2 * y := mul_le_mul_of_nonneg_right hCoef hy0
  have hHalf : d / 2 ≤ y := by linarith only [hDouble]
  have hHalf0 : 0 ≤ d / 2 := by positivity
  have hSq : (d / 2) ^ 2 ≤ y ^ 2 :=
    (sq_le_sq₀ hHalf0 hy0).2 hHalf
  have hPyth : ‖x‖ ^ 2 = ‖F.starProjection x‖ ^ 2 + y ^ 2 := by
    have h := F.norm_sq_eq_add_norm_sq_starProjection x
    change ‖x‖ ^ 2 = ‖F.starProjection x‖ ^ 2 + y ^ 2 at h
    exact h
  change ‖F.starProjection x‖ ^ 2 + (d / 2) ^ 2 ≤ ‖x‖ ^ 2
  linarith only [hSq, hPyth]

local notation "GV" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AJV_group : IsTopologicalGroup GV :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AJV_compact : CompactSpace GV :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AJV_secondCountable : SecondCountableTopology GV :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AJV_measurable : MeasurableSpace GV :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AJV_borel : BorelSpace GV :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AJV_linkFintype (K : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink K) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "PhysV" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "CfgV" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muV" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "fV" =>
  p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "SV" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "RV" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator H 2 (by norm_num)
local notation "OmegaV" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector H 2 (by norm_num)
local notation "VV" =>
  p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "uV" =>
  p4Q2PZ37AIW_originalNormalizedSourceTransfer H
local notation "mV" =>
  p4Q2PZ37AIW_originalNormalizedNegativeMargin H
local notation "dV" =>
  p4Q2PZ37AJU_originalDefectFloor H

local instance p4Q2PZ37AJV_physicalComplete (K : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule K 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    K 2).completeSpace_coe

local instance p4Q2PZ37AJV_topComplete
    (K : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
        K 2 (by norm_num) beta hbeta) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_isClosed
    K 2 (by norm_num) beta hbeta).completeSpace_coe

/-- Fully explicit q-free genuine original-source correction, positive
at every finite H and beta>0 with no unknown operator norm in it. -/
def p4Q2PZ37AJV_originalQFreeCorrection (beta : ℝ) : ℝ :=
  (dV beta / 2) ^ 2

theorem p4Q2PZ37AJV_originalQFreeCorrection_pos
    (beta : ℝ) (hbeta : 0 < beta) :
    0 < p4Q2PZ37AJV_originalQFreeCorrection H beta := by
  unfold p4Q2PZ37AJV_originalQFreeCorrection
  exact sq_pos_of_pos
    (div_pos (p4Q2PZ37AJU_originalDefectFloor_pos H beta hbeta)
      (by norm_num))

/-- Full true top projection of the ORIGINAL signed centered physical ZW
source has an unconditional q-FREE numerical-geometric correction. -/
theorem p4Q2PZ37AJV_originalFullTop_sq_add_qfree_le_variance
    (beta : ℝ) (hbeta : 0 < beta) :
    ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 +
      p4Q2PZ37AJV_originalQFreeCorrection H beta ≤ VV := by
  let S : PhysV →L[ℝ] PhysV := SV beta hbeta.le
  let F : Submodule ℝ PhysV := realHilbertTopEigenspace S
  let hS : (S : PhysV →ₗ[ℝ] PhysV).IsSymmetric :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H 2 (by norm_num) beta hbeta.le
  let R := realHilbertTopEigenspaceOrthogonalRestriction S hS
  letI : CompleteSpace F := (realHilbertTopEigenspace_isClosed S).completeSpace_coe
  letI : CompleteSpace Fᗮ := F.isClosed_orthogonal.completeSpace_coe
  have hq : ‖R‖ ≤ 1 := le_of_lt
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
      H 2 (by norm_num) beta hbeta.le)
  have hd0 : 0 ≤ dV beta :=
    (p4Q2PZ37AJU_originalDefectFloor_pos H beta hbeta).le
  have hd : dV beta ≤ ‖fV - S fV‖ :=
    p4Q2PZ37AJU_originalDefectFloor_le_physicalDefect H beta hbeta
  have h := realHilbert_fullTop_qfree_defect_sq_budget_ajv
    S hS hq fV (dV beta) hd0 hd
  change
    ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 +
      p4Q2PZ37AJV_originalQFreeCorrection H beta ≤ ‖fV‖ ^ 2 at h
  rw [p4Q2PZ37AJR_originalSource_norm_sq_eq_HaarVariance H] at h
  exact h

theorem p4Q2PZ37AJV_originalFullTop_sq_le_qfree_upper
    (beta : ℝ) (hbeta : 0 < beta) :
    ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 ≤
      VV - p4Q2PZ37AJV_originalQFreeCorrection H beta := by
  have h := p4Q2PZ37AJV_originalFullTop_sq_add_qfree_le_variance H beta hbeta
  linarith only [h]

/-- Extra-top residual remains an independent genuine component;
the original selected top overlap is subtracted separately. -/
theorem p4Q2PZ37AJV_originalExtraTop_sq_le_qfree_upper
    (beta : ℝ) (hbeta : 0 < beta) :
    ‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ^ 2 ≤
      VV - (inner ℝ fV (OmegaV beta hbeta.le)) ^ 2 -
        p4Q2PZ37AJV_originalQFreeCorrection H beta := by
  have hBudget :=
    p4Q2PZ37AJV_originalFullTop_sq_add_qfree_le_variance H beta hbeta
  have hSplit :=
    p4Q2PZ37AJF_originalSourceTop_norm_sq_eq_selected_add_extra H beta hbeta
  rw [hSplit] at hBudget
  linarith only [hBudget]

/-- All-top source energy is strictly below its original Haar variance
with a fully specified positive q-free correction, not merely some
unquantified strictness statement. -/
theorem p4Q2PZ37AJV_originalFullTop_sq_strict_lt_variance
    (beta : ℝ) (hbeta : 0 < beta) :
    ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 < VV := by
  have hBudget :=
    p4Q2PZ37AJV_originalFullTop_sq_add_qfree_le_variance H beta hbeta
  have hPos := p4Q2PZ37AJV_originalQFreeCorrection_pos H beta hbeta
  linarith only [hBudget, hPos]

/-- This is a TESTABLE sufficient q-free inequality on the unchanged AJA
budget, not a proved evaluation of that budget. Under it AJI yields
existence of SOME true finite Wilson power; it does not pick n=2. -/
theorem p4Q2PZ37AJV_originalQFreeAJA_strictThreshold_implies_exists_power
    (beta : ℝ) (hbeta : 0 < beta)
    (hThreshold :
      VV - p4Q2PZ37AJV_originalQFreeCorrection H beta <
        (mV beta hbeta.le) ^ 2 *
          Measure.real muV
            {B : CfgV | uV beta hbeta.le B < -(mV beta hbeta.le)}) :
    ∃ n : ℕ, 0 < n ∧
      ‖((SV beta hbeta.le) ^ n) fV‖ ^ 2 <
        (mV beta hbeta.le) ^ 2 *
          Measure.real muV
            {B : CfgV | uV beta hbeta.le B < -(mV beta hbeta.le)} := by
  have hTop : ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 <
      (mV beta hbeta.le) ^ 2 *
        Measure.real muV
          {B : CfgV | uV beta hbeta.le B < -(mV beta hbeta.le)} :=
    (p4Q2PZ37AJV_originalFullTop_sq_le_qfree_upper
      H beta hbeta).trans_lt hThreshold
  exact (p4Q2PZ37AJI_fullTop_small_iff_exists_transferPower_budget
    H beta hbeta).1 hTop

/-- Conditional genuine *transferred* full-top-orthogonal source
nonvanishing. Unconditional PRE-transfer source nonvanishing from AJQ
does not, without further proof, imply this conclusion. -/
theorem p4Q2PZ37AJV_originalTransferredOrthogonal_ne_zero_of_qfreeThreshold
    (beta : ℝ) (hbeta : 0 < beta)
    (hThreshold :
      VV - p4Q2PZ37AJV_originalQFreeCorrection H beta <
        (mV beta hbeta.le) ^ 2 *
          Measure.real muV
            {B : CfgV | uV beta hbeta.le B < -(mV beta hbeta.le)}) :
    p4Q2PZ37AJC_originalNormalizedSourceOrthogonalComponent H beta hbeta ≠ 0 := by
  exact
    p4Q2PZ37AJI_originalOrthogonal_ne_zero_of_exists_transferPower_budget
      H beta hbeta
        (p4Q2PZ37AJV_originalQFreeAJA_strictThreshold_implies_exists_power
          H beta hbeta hThreshold)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

/-! Exactly nine new definitions or theorems; all are audited against the Lean kernel. -/
#print axioms MGAP4D.MathlibAnalytic.realHilbert_fullTop_qfree_defect_sq_budget_ajv
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJV_originalQFreeCorrection
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJV_originalQFreeCorrection_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJV_originalFullTop_sq_add_qfree_le_variance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJV_originalFullTop_sq_le_qfree_upper
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJV_originalExtraTop_sq_le_qfree_upper
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJV_originalFullTop_sq_strict_lt_variance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJV_originalQFreeAJA_strictThreshold_implies_exists_power
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJV_originalTransferredOrthogonal_ne_zero_of_qfreeThreshold
