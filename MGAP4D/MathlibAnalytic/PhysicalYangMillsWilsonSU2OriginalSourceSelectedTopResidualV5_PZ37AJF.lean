import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFullTopOverlapDualBoundsV5_PZ37AJE
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AJF — selected genuine top direction versus extra full-top residual

The ORIGINAL centered signed ZW Gauss-law physical source, the original
complete SU(2) Wilson one-slab operator, its symmetric normalized transfer,
and its unchanged full fixed-point/top eigenspace remain untouched.

AJE gives the exact bound on the full top projection through *all* actual
top vectors. Here we refine the obstruction by separating the already
existing selected UNIT top eigenvector from the remaining actual full-top
part. This is an identity, not a claim of vacuum uniqueness or top simplicity.

In particular, an observed small overlap with one selected eigenvector does
not bound the other full-top directions. No extra hypothesis, substitute
physical source, volume-uniform gap, or mass-gap claim is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Exact real-Hilbert Pythagoras along an ACTUAL unit vector.
The coefficient is the true ambient inner product. -/
theorem realHilbert_unitDirection_norm_sq_split
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x omega : E) (homega : ‖omega‖ = 1) :
    ‖x‖ ^ 2 =
      (inner ℝ x omega) ^ 2 +
        ‖x - (inner ℝ x omega) • omega‖ ^ 2 := by
  have hinner :
      inner ℝ x ((inner ℝ x omega) • omega) =
        (inner ℝ x omega) ^ 2 := by
    rw [real_inner_smul_right]
    ring
  have hnorm :
      ‖(inner ℝ x omega) • omega‖ ^ 2 =
        (inner ℝ x omega) ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, homega, mul_one]
    exact sq_abs _
  have hdiff := norm_sub_sq_real x ((inner ℝ x omega) • omega)
  rw [hinner, hnorm] at hdiff
  nlinarith

/-- An ACTUAL closed-subspace projection splits into its selected unit
direction and an orthogonal residual. No one-dimensionality assumption. -/
theorem realHilbert_starProjection_unitDirection_norm_sq_split
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : Submodule ℝ E) [F.HasOrthogonalProjection]
    (x omega : E) (homegaMem : omega ∈ F) (homega : ‖omega‖ = 1) :
    ‖F.starProjection x‖ ^ 2 =
      (inner ℝ x omega) ^ 2 +
      ‖F.starProjection x - (inner ℝ x omega) • omega‖ ^ 2 := by
  have hi : inner ℝ (F.starProjection x) omega = inner ℝ x omega :=
    (realHilbert_starProjection_inner_eq_of_mem F x omega homegaMem).symm
  simpa only [hi] using
    (realHilbert_unitDirection_norm_sq_split (F.starProjection x) omega homega)

/-- The extra top residual is truly orthogonal to the selected unit
vector, even though it is not assumed to vanish. -/
theorem realHilbert_starProjection_unitDirection_residual_inner_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : Submodule ℝ E) [F.HasOrthogonalProjection]
    (x omega : E) (homegaMem : omega ∈ F) (homega : ‖omega‖ = 1) :
    inner ℝ
      (F.starProjection x - (inner ℝ x omega) • omega) omega = 0 := by
  have hi : inner ℝ (F.starProjection x) omega = inner ℝ x omega :=
    (realHilbert_starProjection_inner_eq_of_mem F x omega homegaMem).symm
  have hself : inner ℝ omega omega = 1 := by
    rw [real_inner_self_eq_norm_sq, homega]
    norm_num
  rw [inner_sub_left, real_inner_smul_left, hi, hself]
  ring

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "PhysF" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "CfgF" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muF" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "fF" =>
  p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "TopF" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace H 2 (by norm_num)
local notation "OmegaF" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector H 2 (by norm_num)
local notation "uF" =>
  p4Q2PZ37AIW_originalNormalizedSourceTransfer H
local notation "mF" =>
  p4Q2PZ37AIW_originalNormalizedNegativeMargin H

local instance p4Q2PZ37AJF_physicalComplete (K : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule K 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    K 2).completeSpace_coe

local instance p4Q2PZ37AJF_topComplete
    (K : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
        K 2 (by norm_num) beta hbeta) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_isClosed
    K 2 (by norm_num) beta hbeta).completeSpace_coe

/-- The EXTRA top component of the ORIGINAL ZW source after removing
only its real overlap with the already existing chosen UNIT top vector. -/
noncomputable def p4Q2PZ37AJF_originalSourceExtraTopComponent
    (beta : ℝ) (hbeta : 0 < beta) : PhysF :=
  p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta -
    (inner ℝ fF (OmegaF beta hbeta.le)) • (OmegaF beta hbeta.le)

/-- The residual after removing the chosen top direction still lies
in the unchanged entire top eigenspace. -/
theorem p4Q2PZ37AJF_originalSourceExtraTop_mem
    (beta : ℝ) (hbeta : 0 < beta) :
    p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta ∈
      TopF beta hbeta.le := by
  change (TopF beta hbeta.le).starProjection fF -
    (inner ℝ fF (OmegaF beta hbeta.le)) • (OmegaF beta hbeta.le) ∈
      TopF beta hbeta.le
  exact (TopF beta hbeta.le).sub_mem
    ((TopF beta hbeta.le).starProjection_apply_mem fF)
    ((TopF beta hbeta.le).smul_mem _
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_mem_topEigenspace
        H 2 (by norm_num) beta hbeta.le))

/-- The genuine extra-top residual is orthogonal to the chosen unit
top vector, with no assumption that the extra component vanishes. -/
theorem p4Q2PZ37AJF_originalSourceExtraTop_inner_selected_eq_zero
    (beta : ℝ) (hbeta : 0 < beta) :
    inner ℝ
      (p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta)
      (OmegaF beta hbeta.le) = 0 := by
  change inner ℝ
    ((TopF beta hbeta.le).starProjection fF -
      (inner ℝ fF (OmegaF beta hbeta.le)) • (OmegaF beta hbeta.le))
    (OmegaF beta hbeta.le) = 0
  exact realHilbert_starProjection_unitDirection_residual_inner_zero
    (TopF beta hbeta.le) fF (OmegaF beta hbeta.le)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_mem_topEigenspace
      H 2 (by norm_num) beta hbeta.le)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_norm
      H 2 (by norm_num) beta hbeta.le)

/-- The ACTUAL source's entire top projection has exactly TWO
orthogonal contributions: selected vacuum-direction overlap and
an extra-top residual. Neither contribution is assumed small. -/
theorem p4Q2PZ37AJF_originalSourceTop_norm_sq_eq_selected_add_extra
    (beta : ℝ) (hbeta : 0 < beta) :
    ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 =
      (inner ℝ fF (OmegaF beta hbeta.le)) ^ 2 +
      ‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ^ 2 := by
  change ‖(TopF beta hbeta.le).starProjection fF‖ ^ 2 =
    (inner ℝ fF (OmegaF beta hbeta.le)) ^ 2 +
    ‖(TopF beta hbeta.le).starProjection fF -
      (inner ℝ fF (OmegaF beta hbeta.le)) • (OmegaF beta hbeta.le)‖ ^ 2
  exact realHilbert_starProjection_unitDirection_norm_sq_split
    (TopF beta hbeta.le) fF (OmegaF beta hbeta.le)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_mem_topEigenspace
      H 2 (by norm_num) beta hbeta.le)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_norm
      H 2 (by norm_num) beta hbeta.le)

/-- Rewrite the existing ORIGINAL AJA Haar-L2 certificate by subtracting
BOTH true top obstructions: the selected unit mode and the extra top. -/
theorem p4Q2PZ37AJF_originalOrthogonal_norm_sq_ge_certificate_sub_selected_extra
    (beta : ℝ) (hbeta : 0 < beta) :
    (mF beta hbeta.le) ^ 2 *
      Measure.real muF
        {B : CfgF | uF beta hbeta.le B < -(mF beta hbeta.le)} -
      ((inner ℝ fF (OmegaF beta hbeta.le)) ^ 2 +
      ‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ^ 2)
    ≤ ‖p4Q2PZ37AJC_originalNormalizedSourceOrthogonalComponent H beta hbeta‖ ^ 2 := by
  have h :=
    p4Q2PZ37AJD_originalOrthogonal_norm_sq_ge_certificate_sub_sourceTop
      H beta hbeta
  rw [p4Q2PZ37AJF_originalSourceTop_norm_sq_eq_selected_add_extra H beta hbeta] at h
  exact h

/-- A strict upper bound for BOTH genuinely distinct top contributions
would imply nonzero orthogonal normalized source, but is not provided here. -/
theorem p4Q2PZ37AJF_originalOrthogonal_ne_zero_of_selected_extra_budget
    (beta : ℝ) (hbeta : 0 < beta)
    (hBudget :
      (inner ℝ fF (OmegaF beta hbeta.le)) ^ 2 +
        ‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ^ 2 <
      (mF beta hbeta.le) ^ 2 *
        Measure.real muF
          {B : CfgF | uF beta hbeta.le B < -(mF beta hbeta.le)}) :
    p4Q2PZ37AJC_originalNormalizedSourceOrthogonalComponent H beta hbeta ≠ 0 := by
  apply p4Q2PZ37AJD_orthogonal_ne_zero_of_originalSourceTop_small H beta hbeta
  rw [p4Q2PZ37AJF_originalSourceTop_norm_sq_eq_selected_add_extra H beta hbeta]
  exact hBudget

/-- A genuinely small full-top projection NECESSARILY has a small
selected unit-mode overlap; the converse requires extra-top control. -/
theorem p4Q2PZ37AJF_selected_overlap_sq_lt_certificate_of_fullTop_small
    (beta : ℝ) (hbeta : 0 < beta)
    (hSmall :
      ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 <
        (mF beta hbeta.le) ^ 2 *
          Measure.real muF
            {B : CfgF | uF beta hbeta.le B < -(mF beta hbeta.le)}) :
    (inner ℝ fF (OmegaF beta hbeta.le)) ^ 2 <
      (mF beta hbeta.le) ^ 2 *
        Measure.real muF
          {B : CfgF | uF beta hbeta.le B < -(mF beta hbeta.le)} := by
  have hsplit :=
    p4Q2PZ37AJF_originalSourceTop_norm_sq_eq_selected_add_extra H beta hbeta
  have hres :
      0 ≤ ‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ^ 2 :=
    sq_nonneg _
  linarith

/-- If the selected true top unit-mode alone exceeds the original
Haar certificate, the desired FULL-top-small antecedent is obstructed.
This is a necessary-test no-go, NOT a claim that excitation is zero. -/
theorem p4Q2PZ37AJF_no_fullTop_small_of_selected_overlap_large
    (beta : ℝ) (hbeta : 0 < beta)
    (hLarge :
      (mF beta hbeta.le) ^ 2 *
        Measure.real muF
          {B : CfgF | uF beta hbeta.le B < -(mF beta hbeta.le)}
        ≤ (inner ℝ fF (OmegaF beta hbeta.le)) ^ 2) :
    ¬ (‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 <
      (mF beta hbeta.le) ^ 2 *
        Measure.real muF
          {B : CfgF | uF beta hbeta.le B < -(mF beta hbeta.le)}) := by
  intro hsmall
  have hs :=
    p4Q2PZ37AJF_selected_overlap_sq_lt_certificate_of_fullTop_small
      H beta hbeta hsmall
  exact (not_lt_of_ge hLarge) hs

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

/-! New declaration dependency inspection — no additional axioms. -/
#print axioms MGAP4D.MathlibAnalytic.realHilbert_unitDirection_norm_sq_split
#print axioms MGAP4D.MathlibAnalytic.realHilbert_starProjection_unitDirection_norm_sq_split
#print axioms MGAP4D.MathlibAnalytic.realHilbert_starProjection_unitDirection_residual_inner_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJF_originalSourceExtraTopComponent
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJF_originalSourceExtraTop_mem
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJF_originalSourceExtraTop_inner_selected_eq_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJF_originalSourceTop_norm_sq_eq_selected_add_extra
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJF_originalOrthogonal_norm_sq_ge_certificate_sub_selected_extra
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJF_originalOrthogonal_ne_zero_of_selected_extra_budget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJF_selected_overlap_sq_lt_certificate_of_fullTop_small
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJF_no_fullTop_small_of_selected_overlap_large
