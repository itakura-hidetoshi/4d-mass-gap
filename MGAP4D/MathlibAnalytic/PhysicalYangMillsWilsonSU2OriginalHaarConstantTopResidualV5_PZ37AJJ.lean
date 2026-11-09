import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSourceFullTopPowerLimitV5_PZ37AJI
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AJJ — genuine Haar constant defect and full-top residual

At every original finite H and positive beta, work in the original
Gauss-law SU(2) physical real Hilbert space with the ORIGINAL norm-one
symmetric, positive, compact Wilson transfer and full fixed eigenspace.
The existing orthogonal restriction R satisfies norm R < 1.

Its spectral separation controls the distance of the Haar-constant unit
vector c to the WHOLE top eigenspace:
  (1 - norm R) * norm (Q_orth c) <= norm (c - S c).

This must NOT be promoted to a selected-vacuum closeness result. We
instead split the selected-vacuum deviation exactly into the full-top
orthogonal distance AND a separately named extra-top constant residual.
We then carry both terms into the ORIGINAL centered ZW source's AJG upper
bound. No unproved top simplicity, residual vanishing, uniform rate,
AJA strict budget, or continuum Yang-Mills gap is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- The actual full-fixed top orthogonal component is bounded by the
unmodified operator defect, multiplied by the spectral-separation factor.
This statement does not assume that the fixed space is one dimensional. -/
theorem realHilbert_fullTop_gap_mul_distance_le_defect_ajj
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : E →L[ℝ] E)
    [(realHilbertTopEigenspace S).HasOrthogonalProjection]
    (hSymm : (S : E →ₗ[ℝ] E).IsSymmetric)
    (c : E) :
    (1 - ‖realHilbertTopEigenspaceOrthogonalRestriction S hSymm‖) *
      ‖((realHilbertTopEigenspace S)ᗮ).starProjection c‖ ≤
      ‖c - S c‖ := by
  let F := realHilbertTopEigenspace S
  let R := realHilbertTopEigenspaceOrthogonalRestriction S hSymm
  let t : E := F.starProjection c
  let y : Fᗮ :=
    ⟨(Fᗮ).starProjection c, (Fᗮ).starProjection_apply_mem c⟩
  have hsplit : t + (y : E) = c :=
    F.starProjection_add_starProjection_orthogonal c
  have ht : t ∈ F := F.starProjection_apply_mem c
  have hfix : S t = t := (realHilbertTopEigenspace_mem S t).mp ht
  have hcoe : ((R y : Fᗮ) : E) = S (y : E) :=
    realHilbertTopEigenspaceOrthogonalRestriction_coe S hSymm y
  have hR : ‖S (y : E)‖ ≤ ‖R‖ * ‖(y : E)‖ := by
    calc
      ‖S (y : E)‖ = ‖R y‖ := by rw [← hcoe]; rfl
      _ ≤ ‖R‖ * ‖y‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖R‖ * ‖(y : E)‖ := rfl
  have hdiff : (y : E) - S (y : E) = c - S c := by
    calc
      (y : E) - S (y : E) =
          (t + (y : E)) - S (t + (y : E)) := by
            rw [map_add, hfix]
            abel
      _ = c - S c := by rw [hsplit]
  have htri : ‖(y : E)‖ ≤ ‖c - S c‖ + ‖S (y : E)‖ := by
    calc
      ‖(y : E)‖ =
          ‖((y : E) - S (y : E)) + S (y : E)‖ := by
            rw [sub_add_cancel]
      _ ≤ ‖(y : E) - S (y : E)‖ + ‖S (y : E)‖ :=
        norm_add_le _ _
      _ = ‖c - S c‖ + ‖S (y : E)‖ := by rw [hdiff]
  change (1 - ‖R‖) * ‖(y : E)‖ ≤ ‖c - S c‖
  nlinarith [htri, hR]

/-- The same top-orthogonal distance admits a genuine quotient bound
whenever the actual full-top orthogonal restriction has norm < 1. -/
theorem realHilbert_fullTop_distance_le_defect_div_gap_ajj
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : E →L[ℝ] E)
    [(realHilbertTopEigenspace S).HasOrthogonalProjection]
    (hSymm : (S : E →ₗ[ℝ] E).IsSymmetric)
    (hq : ‖realHilbertTopEigenspaceOrthogonalRestriction S hSymm‖ < 1)
    (c : E) :
    ‖((realHilbertTopEigenspace S)ᗮ).starProjection c‖ ≤
      ‖c - S c‖ /
        (1 - ‖realHilbertTopEigenspaceOrthogonalRestriction S hSymm‖) := by
  have hgap :
      0 < 1 - ‖realHilbertTopEigenspaceOrthogonalRestriction S hSymm‖ :=
    sub_pos.mpr hq
  have hbound :=
    realHilbert_fullTop_gap_mul_distance_le_defect_ajj S hSymm c
  exact (le_div_iff₀ hgap).2 (by simpa only [mul_comm] using hbound)

/-- A chosen unit vector IN the full top eigenspace need not span it.
The selected-direction deviation splits exactly into full-top distance
and the extra TOP-part of the constant orthogonal to that choice. -/
theorem realHilbert_unitConstant_selectedTop_deviation_sq_split_ajj
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : Submodule ℝ E) [F.HasOrthogonalProjection]
    (c omega : E) (hc : ‖c‖ = 1)
    (homega : ‖omega‖ = 1) (homegaMem : omega ∈ F) :
    1 - (inner ℝ omega c) ^ 2 =
      ‖(Fᗮ).starProjection c‖ ^ 2 +
        ‖F.starProjection c - (inner ℝ c omega) • omega‖ ^ 2 := by
  have hP := F.norm_sq_eq_add_norm_sq_starProjection c
  have hQ :=
    realHilbert_starProjection_unitDirection_norm_sq_split
      F c omega homegaMem homega
  rw [hc] at hP
  have hSymm : inner ℝ omega c = inner ℝ c omega :=
    (real_inner_comm omega c).symm
  rw [hSymm]
  norm_num at hP
  linarith [hP, hQ]

/-- In the original full-top geometry, the squared selected deviation
is controlled from above by the true (I-S)c residual DIVIDED by the
actual finite-volume full-top spectral separation, PLUS the independent
selected-vacuum extra-top constant residual. It is not set to zero. -/
theorem realHilbert_selectedTop_deviation_sq_le_defect_extra_ajj
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : E →L[ℝ] E)
    [(realHilbertTopEigenspace S).HasOrthogonalProjection]
    (hSymm : (S : E →ₗ[ℝ] E).IsSymmetric)
    (hq : ‖realHilbertTopEigenspaceOrthogonalRestriction S hSymm‖ < 1)
    (c omega : E) (hc : ‖c‖ = 1)
    (homega : ‖omega‖ = 1)
    (homegaMem : omega ∈ realHilbertTopEigenspace S) :
    1 - (inner ℝ omega c) ^ 2 ≤
      (‖c - S c‖ /
        (1 - ‖realHilbertTopEigenspaceOrthogonalRestriction S hSymm‖)) ^ 2 +
      ‖(realHilbertTopEigenspace S).starProjection c -
        (inner ℝ c omega) • omega‖ ^ 2 := by
  let F := realHilbertTopEigenspace S
  let R := realHilbertTopEigenspaceOrthogonalRestriction S hSymm
  have hsplit :=
    realHilbert_unitConstant_selectedTop_deviation_sq_split_ajj
      F c omega hc homega homegaMem
  have hup :
      ‖(Fᗮ).starProjection c‖ ≤ ‖c - S c‖ / (1 - ‖R‖) :=
    realHilbert_fullTop_distance_le_defect_div_gap_ajj S hSymm hq c
  have hgap : 0 < 1 - ‖R‖ := sub_pos.mpr hq
  have hfrac : 0 ≤ ‖c - S c‖ / (1 - ‖R‖) :=
    div_nonneg (norm_nonneg _) hgap.le
  have hsq :
      ‖(Fᗮ).starProjection c‖ ^ 2 ≤
        (‖c - S c‖ / (1 - ‖R‖)) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hup)
      (add_nonneg (norm_nonneg ((Fᗮ).starProjection c)) hfrac)]
  calc
    1 - (inner ℝ omega c) ^ 2 =
        ‖(Fᗮ).starProjection c‖ ^ 2 +
          ‖F.starProjection c - (inner ℝ c omega) • omega‖ ^ 2 := hsplit
    _ ≤ (‖c - S c‖ / (1 - ‖R‖)) ^ 2 +
          ‖F.starProjection c - (inner ℝ c omega) • omega‖ ^ 2 :=
      add_le_add_left hsq _

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "PhysJ" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "CfgJ" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muJ" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "fJ" =>
  p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "cJ" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
local notation "TopJ" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace H 2 (by norm_num)
local notation "OmegaJ" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector H 2 (by norm_num)
local notation "SJ" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "RJ" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator H 2 (by norm_num)
local notation "uJ" => p4Q2PZ37AIW_originalNormalizedSourceTransfer H
local notation "mJ" => p4Q2PZ37AIW_originalNormalizedNegativeMargin H

local instance p4Q2PZ37AJJ_physicalComplete (K : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule K 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    K 2).completeSpace_coe

local instance p4Q2PZ37AJJ_topComplete
    (K : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
        K 2 (by norm_num) beta hbeta) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_isClosed
    K 2 (by norm_num) beta hbeta).completeSpace_coe

/-- The residual of the ORIGINAL Haar constant in the ENTIRE genuine
top eigenspace, after removing only the already selected unit top vector.
This is distinct from AJF's residual of the centered ZW source. -/
noncomputable def p4Q2PZ37AJJ_originalHaarConstantExtraTopComponent
    (beta : ℝ) (hbeta : 0 < beta) : PhysJ :=
  (TopJ beta hbeta.le).starProjection cJ -
    (inner ℝ cJ (OmegaJ beta hbeta.le)) • (OmegaJ beta hbeta.le)

/-- The extra component of the Haar constant is genuinely in the
unmodified complete fixed eigenspace. No top simplicity assertion. -/
theorem p4Q2PZ37AJJ_originalHaarConstantExtraTop_mem
    (beta : ℝ) (hbeta : 0 < beta) :
    p4Q2PZ37AJJ_originalHaarConstantExtraTopComponent H beta hbeta ∈
      TopJ beta hbeta.le := by
  change (TopJ beta hbeta.le).starProjection cJ -
    (inner ℝ cJ (OmegaJ beta hbeta.le)) • (OmegaJ beta hbeta.le) ∈
      TopJ beta hbeta.le
  exact (TopJ beta hbeta.le).sub_mem
    ((TopJ beta hbeta.le).starProjection_apply_mem cJ)
    ((TopJ beta hbeta.le).smul_mem _
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_mem_topEigenspace
        H 2 (by norm_num) beta hbeta.le))

/-- Genuine finite-volume separation, already proven by positivity
and compactness, now displayed as the coefficient of a defect bound. -/
theorem p4Q2PZ37AJJ_originalFullTopResidualGap_pos
    (beta : ℝ) (hbeta : 0 < beta) :
    0 < 1 - ‖RJ beta hbeta.le‖ :=
  sub_pos.mpr
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
      H 2 (by norm_num) beta hbeta.le)

/-- The actual ORIGINAL Haar-constant vector's physical distance from
the WHOLE top subspace has an explicit, finite-H beta>0 upper bound
using the unchanged original physical Wilson transfer. -/
theorem p4Q2PZ37AJJ_originalHaarConstant_gap_mul_fullTopDistance_le_defect
    (beta : ℝ) (hbeta : 0 < beta) :
    (1 - ‖RJ beta hbeta.le‖) *
      ‖((TopJ beta hbeta.le)ᗮ).starProjection cJ‖ ≤
      ‖cJ - (SJ beta hbeta.le) cJ‖ := by
  let S : PhysJ →L[ℝ] PhysJ := SJ beta hbeta.le
  let hS : (S : PhysJ →ₗ[ℝ] PhysJ).IsSymmetric :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H 2 (by norm_num) beta hbeta.le
  let F : Submodule ℝ PhysJ := realHilbertTopEigenspace S
  let R := realHilbertTopEigenspaceOrthogonalRestriction S hS
  letI : CompleteSpace F :=
    (realHilbertTopEigenspace_isClosed S).completeSpace_coe
  change (1 - ‖R‖) * ‖(Fᗮ).starProjection cJ‖ ≤ ‖cJ - S cJ‖
  exact realHilbert_fullTop_gap_mul_distance_le_defect_ajj S hS cJ

/-- An honest ORIGINAL-Wilson upper bound for the entire full-top
orthogonal Haar-constant distance. The denominator is strictly positive
at every fixed H,beta from already certified physical results. -/
theorem p4Q2PZ37AJJ_originalHaarConstant_fullTopDistance_le_defect_div_gap
    (beta : ℝ) (hbeta : 0 < beta) :
    ‖((TopJ beta hbeta.le)ᗮ).starProjection cJ‖ ≤
      ‖cJ - (SJ beta hbeta.le) cJ‖ /
        (1 - ‖RJ beta hbeta.le‖) := by
  have hgap := p4Q2PZ37AJJ_originalFullTopResidualGap_pos H beta hbeta
  have hdef :=
    p4Q2PZ37AJJ_originalHaarConstant_gap_mul_fullTopDistance_le_defect
      H beta hbeta
  exact (le_div_iff₀ hgap).2 (by simpa only [mul_comm] using hdef)

/-- Exact splitting of the ORIGINAL selected top-vacuum deviation into
two independent true physical nonnegative norm squares: the full-top
orthogonal Haar-constant distance and the extra TOP constant residual. -/
theorem p4Q2PZ37AJJ_originalSelectedVacuumDeviation_eq_fullTop_add_extra
    (beta : ℝ) (hbeta : 0 < beta) :
    1 - (inner ℝ (OmegaJ beta hbeta.le) cJ) ^ 2 =
      ‖((TopJ beta hbeta.le)ᗮ).starProjection cJ‖ ^ 2 +
      ‖p4Q2PZ37AJJ_originalHaarConstantExtraTopComponent H beta hbeta‖ ^ 2 := by
  let F : Submodule ℝ PhysJ := TopJ beta hbeta.le
  letI : CompleteSpace F :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_isClosed
      H 2 (by norm_num) beta hbeta.le).completeSpace_coe
  change 1 - (inner ℝ (OmegaJ beta hbeta.le) cJ) ^ 2 =
    ‖(Fᗮ).starProjection cJ‖ ^ 2 +
      ‖F.starProjection cJ -
        (inner ℝ cJ (OmegaJ beta hbeta.le)) • (OmegaJ beta hbeta.le)‖ ^ 2
  exact realHilbert_unitConstant_selectedTop_deviation_sq_split_ajj
    F cJ (OmegaJ beta hbeta.le)
    (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm H 2)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_norm
      H 2 (by norm_num) beta hbeta.le)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_mem_topEigenspace
      H 2 (by norm_num) beta hbeta.le)

/-- The selected top-vacuum constant deviation DOES have an upper bound
from the true (I-S)c defect, but it MUST retain the separate extra-top
constant residual. Neither its size nor its vanishing is certified. -/
theorem p4Q2PZ37AJJ_originalSelectedVacuumDeviation_le_defect_extra
    (beta : ℝ) (hbeta : 0 < beta) :
    1 - (inner ℝ (OmegaJ beta hbeta.le) cJ) ^ 2 ≤
      (‖cJ - (SJ beta hbeta.le) cJ‖ /
        (1 - ‖RJ beta hbeta.le‖)) ^ 2 +
      ‖p4Q2PZ37AJJ_originalHaarConstantExtraTopComponent H beta hbeta‖ ^ 2 := by
  have hsplit :=
    p4Q2PZ37AJJ_originalSelectedVacuumDeviation_eq_fullTop_add_extra
      H beta hbeta
  have hdist :=
    p4Q2PZ37AJJ_originalHaarConstant_fullTopDistance_le_defect_div_gap
      H beta hbeta
  have hfrac : 0 ≤ ‖cJ - (SJ beta hbeta.le) cJ‖ /
      (1 - ‖RJ beta hbeta.le‖) :=
    div_nonneg (norm_nonneg _)
      (p4Q2PZ37AJJ_originalFullTopResidualGap_pos H beta hbeta).le
  have hsquared :
      ‖((TopJ beta hbeta.le)ᗮ).starProjection cJ‖ ^ 2 ≤
        (‖cJ - (SJ beta hbeta.le) cJ‖ /
          (1 - ‖RJ beta hbeta.le‖)) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hdist)
      (add_nonneg
        (norm_nonneg (((TopJ beta hbeta.le)ᗮ).starProjection cJ)) hfrac)]
  rw [hsplit]
  exact add_le_add_left hsquared _

/-- AJG's ORIGINAL signed centered ZW-source complete-top bound now
uses the honest original Wilson transfer defect, plus BOTH independent
existing obstructions: extra TOP constant residual and AJF source residual.
No strict AJA certificate comparison is made here. -/
theorem p4Q2PZ37AJJ_originalSourceFullTop_norm_sq_le_defect_extra_const_source
    (beta : ℝ) (hbeta : 0 < beta) :
    ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 ≤
      ‖fJ‖ ^ 2 *
        ((‖cJ - (SJ beta hbeta.le) cJ‖ /
            (1 - ‖RJ beta hbeta.le‖)) ^ 2 +
          ‖p4Q2PZ37AJJ_originalHaarConstantExtraTopComponent
            H beta hbeta‖ ^ 2) +
      ‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ^ 2 := by
  have hAJG :=
    p4Q2PZ37AJG_originalFullTop_norm_sq_le_constantDeviation_add_extra
      H beta hbeta
  have hD :=
    p4Q2PZ37AJJ_originalSelectedVacuumDeviation_le_defect_extra
      H beta hbeta
  have hprod :
      ‖fJ‖ ^ 2 * (1 - (inner ℝ (OmegaJ beta hbeta.le) cJ) ^ 2) ≤
      ‖fJ‖ ^ 2 *
        ((‖cJ - (SJ beta hbeta.le) cJ‖ /
            (1 - ‖RJ beta hbeta.le‖)) ^ 2 +
          ‖p4Q2PZ37AJJ_originalHaarConstantExtraTopComponent
            H beta hbeta‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hD (sq_nonneg _)
  linarith

/-- The full genuine original source orthogonal component is nonzero IF
the three unmodified physical contributions can be certified strictly
below the original AJA Haar-L2 certificate. This strict condition remains
UNPROVEN; it is not a new axiom or a physical hypothesis accepted as fact. -/
theorem p4Q2PZ37AJJ_originalOrthogonal_ne_zero_of_defect_extra_budget
    (beta : ℝ) (hbeta : 0 < beta)
    (hBudget :
      ‖fJ‖ ^ 2 *
          ((‖cJ - (SJ beta hbeta.le) cJ‖ /
              (1 - ‖RJ beta hbeta.le‖)) ^ 2 +
            ‖p4Q2PZ37AJJ_originalHaarConstantExtraTopComponent
              H beta hbeta‖ ^ 2) +
        ‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ^ 2 <
      (mJ beta hbeta.le) ^ 2 *
        Measure.real muJ
          {B : CfgJ | uJ beta hbeta.le B < -(mJ beta hbeta.le)}) :
    p4Q2PZ37AJC_originalNormalizedSourceOrthogonalComponent
      H beta hbeta ≠ 0 := by
  apply p4Q2PZ37AJD_orthogonal_ne_zero_of_originalSourceTop_small
    H beta hbeta
  exact lt_of_le_of_lt
    (p4Q2PZ37AJJ_originalSourceFullTop_norm_sq_le_defect_extra_const_source
      H beta hbeta) hBudget

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

/-! All new declarations require direct kernel axiom-output inspection. -/
#print axioms MGAP4D.MathlibAnalytic.realHilbert_fullTop_gap_mul_distance_le_defect_ajj
#print axioms MGAP4D.MathlibAnalytic.realHilbert_fullTop_distance_le_defect_div_gap_ajj
#print axioms MGAP4D.MathlibAnalytic.realHilbert_unitConstant_selectedTop_deviation_sq_split_ajj
#print axioms MGAP4D.MathlibAnalytic.realHilbert_selectedTop_deviation_sq_le_defect_extra_ajj
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJJ_originalHaarConstantExtraTopComponent
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJJ_originalHaarConstantExtraTop_mem
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJJ_originalFullTopResidualGap_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJJ_originalHaarConstant_gap_mul_fullTopDistance_le_defect
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJJ_originalHaarConstant_fullTopDistance_le_defect_div_gap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJJ_originalSelectedVacuumDeviation_eq_fullTop_add_extra
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJJ_originalSelectedVacuumDeviation_le_defect_extra
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJJ_originalSourceFullTop_norm_sq_le_defect_extra_const_source
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJJ_originalOrthogonal_ne_zero_of_defect_extra_budget
