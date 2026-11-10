import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalOrthogonalPowerSquareBudgetV5_PZ37AJN
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AJO — genuine two-step Wilson square residual budget

AJN split a selected-top finite power exactly into the fixed extra-top
residual and the orthogonal Wilson decay. AJO keeps the SAME original
finite-H SU(2) Wilson physical source, transfer, selected vector, full
top space and orthogonal restriction. It compares two consecutive actual
powers without estimating the unknown orthogonal source norm.

For q = ‖R‖, Dₙ(x) = ‖Sⁿx - ⟨x,Ω⟩Ω‖², and the genuine extra-top square
r(x)², the fixed-space contraction gives

  Dₙ₊₁(x) - q² Dₙ(x) ≤ (1-q²) r(x)²
  r(x)² ≤ Dₙ₊₁(x).

At fixed finite H,beta>0 the PRE-EXISTING strict q<1 permits a genuine
conditional necessary AJA budget obstruction using only two finite power
observations plus the selected overlap. A separate sufficient test is
retained. Neither test is asserted to possess a numerical witness.

No change to the original physical definitions, pinned Lean/mathlib,
source hypotheses or imported files. No rank-one top, vanished residual,
unconditional excitation, H-uniform coercivity or continuum gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open Filter
open scoped InnerProductSpace Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Adjacent actual Wilson powers contract the WHOLE top-orthogonal
tail with the norm of the existing orthogonal restriction. The proof
uses the exact subtype intertwining from AJI, not a replacement model. -/
theorem realHilbert_fullTop_power_tail_step_norm_le_ajo
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E)
    [(realHilbertTopEigenspace S).HasOrthogonalProjection]
    (hSymm : (S : E →ₗ[ℝ] E).IsSymmetric)
    (n : ℕ) (x : E) :
    ‖(S ^ (n + 1)) x - (realHilbertTopEigenspace S).starProjection x‖ ≤
      ‖realHilbertTopEigenspaceOrthogonalRestriction S hSymm‖ *
        ‖(S ^ n) x - (realHilbertTopEigenspace S).starProjection x‖ := by
  let F := realHilbertTopEigenspace S
  let R := realHilbertTopEigenspaceOrthogonalRestriction S hSymm
  letI : CompleteSpace F := (realHilbertTopEigenspace_isClosed S).completeSpace_coe
  letI : CompleteSpace Fᗮ := F.isClosed_orthogonal.completeSpace_coe
  let t : E := F.starProjection x
  let y : Fᗮ :=
    ⟨(Fᗮ).starProjection x, (Fᗮ).starProjection_apply_mem x⟩
  have hDecomp : t + (y : E) = x :=
    F.starProjection_add_starProjection_orthogonal x
  have hFix : ∀ v : E, v ∈ F → S v = v := by
    intro v hv
    exact (realHilbertTopEigenspace_mem S v).mp hv
  have ht : t ∈ F := F.starProjection_apply_mem x
  have hPowerTail (k : ℕ) :
      ‖(S ^ k) x - t‖ = ‖(R ^ k) y‖ := by
    have htPower : (S ^ k) t = t :=
      realHilbert_fixedSubspace_power_fixed_aji F S hFix k t ht
    calc
      ‖(S ^ k) x - t‖ =
          ‖(S ^ k) (t + (y : E)) - t‖ := by rw [hDecomp]
      _ = ‖(S ^ k) (y : E)‖ := by rw [map_add, htPower]; simp
      _ = ‖(R ^ k) y‖ := by
        rw [← realHilbert_topOrthogonalRestriction_power_coe_aji S hSymm k y]
        rfl
  change ‖(S ^ (n + 1)) x - t‖ ≤ ‖R‖ * ‖(S ^ n) x - t‖
  rw [hPowerTail (n + 1), hPowerTail n]
  calc
    ‖(R ^ (n + 1)) y‖ = ‖R ((R ^ n) y)‖ := by
      rw [pow_succ']
      rfl
    _ ≤ ‖R‖ * ‖(R ^ n) y‖ :=
      ContinuousLinearMap.le_opNorm _ _

/-- Square form of the genuine one-step orthogonal power contraction. -/
theorem realHilbert_fullTop_power_tail_step_sq_le_ajo
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E)
    [(realHilbertTopEigenspace S).HasOrthogonalProjection]
    (hSymm : (S : E →ₗ[ℝ] E).IsSymmetric)
    (n : ℕ) (x : E) :
    ‖(S ^ (n + 1)) x - (realHilbertTopEigenspace S).starProjection x‖ ^ 2 ≤
      ‖realHilbertTopEigenspaceOrthogonalRestriction S hSymm‖ ^ 2 *
        ‖(S ^ n) x - (realHilbertTopEigenspace S).starProjection x‖ ^ 2 := by
  have hStep := realHilbert_fullTop_power_tail_step_norm_le_ajo
    S hSymm n x
  have hProduct := mul_nonneg
    (sub_nonneg.mpr hStep)
    (add_nonneg
      (norm_nonneg ((S ^ (n + 1)) x -
        (realHilbertTopEigenspace S).starProjection x))
      (mul_nonneg
        (norm_nonneg (realHilbertTopEigenspaceOrthogonalRestriction S hSymm))
        (norm_nonneg ((S ^ n) x -
          (realHilbertTopEigenspace S).starProjection x))))
  nlinarith

/-- Certified TWO-POWER posterior bracket on the genuine selected
extra-top square, without assuming the selected top spans the full top. -/
theorem realHilbert_selectedPower_sq_twoStep_bracket_ajo
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E)
    [(realHilbertTopEigenspace S).HasOrthogonalProjection]
    (hSymm : (S : E →ₗ[ℝ] E).IsSymmetric)
    (n : ℕ) (x omega : E)
    (homega : omega ∈ realHilbertTopEigenspace S) :
    (‖(S ^ (n + 1)) x - (inner ℝ x omega) • omega‖ ^ 2 -
        ‖realHilbertTopEigenspaceOrthogonalRestriction S hSymm‖ ^ 2 *
          ‖(S ^ n) x - (inner ℝ x omega) • omega‖ ^ 2 ≤
      (1 - ‖realHilbertTopEigenspaceOrthogonalRestriction S hSymm‖ ^ 2) *
        ‖(realHilbertTopEigenspace S).starProjection x -
          (inner ℝ x omega) • omega‖ ^ 2) ∧
    (‖(realHilbertTopEigenspace S).starProjection x -
        (inner ℝ x omega) • omega‖ ^ 2 ≤
      ‖(S ^ (n + 1)) x - (inner ℝ x omega) • omega‖ ^ 2) := by
  let F := realHilbertTopEigenspace S
  letI : CompleteSpace F := (realHilbertTopEigenspace_isClosed S).completeSpace_coe
  have hFix : ∀ v : E, v ∈ F → S v = v := by
    intro v hv
    exact (realHilbertTopEigenspace_mem S v).mp hv
  have hN := realHilbert_fixedSubspace_selectedPower_sq_split_ajn
    F S hSymm hFix n x omega homega
  have hN1 := realHilbert_fixedSubspace_selectedPower_sq_split_ajn
    F S hSymm hFix (n + 1) x omega homega
  have hStepSq := realHilbert_fullTop_power_tail_step_sq_le_ajo
    S hSymm n x
  constructor
  · rw [hN1, hN]
    nlinarith
  · rw [hN1]
    exact le_add_of_nonneg_right (sq_nonneg _)

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "PhysO" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "CfgO" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muO" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "fO" =>
  p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "TopO" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace H 2 (by norm_num)
local notation "OmegaO" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector H 2 (by norm_num)
local notation "SO" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "RO" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator H 2 (by norm_num)
local notation "uO" => p4Q2PZ37AIW_originalNormalizedSourceTransfer H
local notation "mO" => p4Q2PZ37AIW_originalNormalizedNegativeMargin H

local instance p4Q2PZ37AJO_physicalComplete (K : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule K 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    K 2).completeSpace_coe

local instance p4Q2PZ37AJO_topComplete
    (K : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
        K 2 (by norm_num) beta hbeta) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_isClosed
    K 2 (by norm_num) beta hbeta).completeSpace_coe

/-- ORIGINAL centered signed ZW source: two consecutive real Wilson
powers give a direct lower/upper bracket on its genuine extra-top square. -/
theorem p4Q2PZ37AJO_originalSource_twoStep_selected_sq_bracket
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ) :
    (‖((SO beta hbeta.le) ^ (n + 1)) fO -
        (inner ℝ fO (OmegaO beta hbeta.le)) • (OmegaO beta hbeta.le)‖ ^ 2 -
      ‖RO beta hbeta.le‖ ^ 2 *
        ‖((SO beta hbeta.le) ^ n) fO -
          (inner ℝ fO (OmegaO beta hbeta.le)) • (OmegaO beta hbeta.le)‖ ^ 2 ≤
      (1 - ‖RO beta hbeta.le‖ ^ 2) *
        ‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ^ 2) ∧
    (‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ^ 2 ≤
      ‖((SO beta hbeta.le) ^ (n + 1)) fO -
        (inner ℝ fO (OmegaO beta hbeta.le)) • (OmegaO beta hbeta.le)‖ ^ 2) := by
  let S : PhysO →L[ℝ] PhysO := SO beta hbeta.le
  let F : Submodule ℝ PhysO := realHilbertTopEigenspace S
  let hS : (S : PhysO →ₗ[ℝ] PhysO).IsSymmetric :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H 2 (by norm_num) beta hbeta.le
  letI : CompleteSpace F := (realHilbertTopEigenspace_isClosed S).completeSpace_coe
  change
    (‖(S ^ (n + 1)) fO -
        (inner ℝ fO (OmegaO beta hbeta.le)) • (OmegaO beta hbeta.le)‖ ^ 2 -
      ‖realHilbertTopEigenspaceOrthogonalRestriction S hS‖ ^ 2 *
        ‖(S ^ n) fO -
          (inner ℝ fO (OmegaO beta hbeta.le)) • (OmegaO beta hbeta.le)‖ ^ 2 ≤
      (1 - ‖realHilbertTopEigenspaceOrthogonalRestriction S hS‖ ^ 2) *
        ‖F.starProjection fO -
          (inner ℝ fO (OmegaO beta hbeta.le)) • (OmegaO beta hbeta.le)‖ ^ 2) ∧
    (‖F.starProjection fO -
        (inner ℝ fO (OmegaO beta hbeta.le)) • (OmegaO beta hbeta.le)‖ ^ 2 ≤
      ‖(S ^ (n + 1)) fO -
        (inner ℝ fO (OmegaO beta hbeta.le)) • (OmegaO beta hbeta.le)‖ ^ 2)
  exact realHilbert_selectedPower_sq_twoStep_bracket_ajo
    S hS n fO (OmegaO beta hbeta.le)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_mem_topEigenspace
      H 2 (by norm_num) beta hbeta.le)

/-- Conditional SUFFICIENT strict AJA witness from the next genuine
selected-power square alone. No such numerical witness is asserted. -/
theorem p4Q2PZ37AJO_originalSource_nextPower_sq_budget_implies_excitation
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ)
    (hSmall :
      (inner ℝ fO (OmegaO beta hbeta.le)) ^ 2 +
        ‖((SO beta hbeta.le) ^ (n + 1)) fO -
          (inner ℝ fO (OmegaO beta hbeta.le)) • (OmegaO beta hbeta.le)‖ ^ 2 <
      (mO beta hbeta.le) ^ 2 *
        Measure.real muO
          {B : CfgO | uO beta hbeta.le B < -(mO beta hbeta.le)}) :
    p4Q2PZ37AJC_originalNormalizedSourceOrthogonalComponent
      H beta hbeta ≠ 0 := by
  have hBracket :=
    (p4Q2PZ37AJO_originalSource_twoStep_selected_sq_bracket
      H beta hbeta n).2
  have hFull :=
    p4Q2PZ37AJF_originalSourceTop_norm_sq_eq_selected_add_extra H beta hbeta
  apply p4Q2PZ37AJD_orthogonal_ne_zero_of_originalSourceTop_small H beta hbeta
  rw [hFull]
  linarith

/-- TRUE conditional necessary obstruction to the unchanged strict
AJA full-top-small certificate, expressed solely through two actual
consecutive original-source Wilson power measurements, selected overlap
and the EXISTING finite-volume q=‖R‖<1.
Nothing here asserts that the premise can be numerically established. -/
theorem p4Q2PZ37AJO_originalSource_twoStep_sq_budget_obstruction
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ)
    (hLarge :
      (1 - ‖RO beta hbeta.le‖ ^ 2) *
        ((mO beta hbeta.le) ^ 2 *
          Measure.real muO
            {B : CfgO | uO beta hbeta.le B < -(mO beta hbeta.le)}) ≤
      (1 - ‖RO beta hbeta.le‖ ^ 2) *
        (inner ℝ fO (OmegaO beta hbeta.le)) ^ 2 +
        ‖((SO beta hbeta.le) ^ (n + 1)) fO -
          (inner ℝ fO (OmegaO beta hbeta.le)) • (OmegaO beta hbeta.le)‖ ^ 2 -
        ‖RO beta hbeta.le‖ ^ 2 *
          ‖((SO beta hbeta.le) ^ n) fO -
            (inner ℝ fO (OmegaO beta hbeta.le)) • (OmegaO beta hbeta.le)‖ ^ 2) :
    ¬ (‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 <
      (mO beta hbeta.le) ^ 2 *
        Measure.real muO
          {B : CfgO | uO beta hbeta.le B < -(mO beta hbeta.le)}) := by
  have hBracket :=
    (p4Q2PZ37AJO_originalSource_twoStep_selected_sq_bracket
      H beta hbeta n).1
  have hFull :=
    p4Q2PZ37AJF_originalSourceTop_norm_sq_eq_selected_add_extra H beta hbeta
  have hR : ‖RO beta hbeta.le‖ < 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
      H 2 (by norm_num) beta hbeta.le
  have hCoef : 0 < 1 - ‖RO beta hbeta.le‖ ^ 2 := by
    have hNonneg : 0 ≤ ‖RO beta hbeta.le‖ := norm_nonneg (RO beta hbeta.le)
    nlinarith
  intro hSmall
  rw [hFull] at hSmall
  have hUpper :
      (1 - ‖RO beta hbeta.le‖ ^ 2) *
        ((mO beta hbeta.le) ^ 2 *
          Measure.real muO
            {B : CfgO | uO beta hbeta.le B < -(mO beta hbeta.le)}) ≤
      (1 - ‖RO beta hbeta.le‖ ^ 2) *
        ((inner ℝ fO (OmegaO beta hbeta.le)) ^ 2 +
          ‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ^ 2) := by
    calc
      _ ≤
        (1 - ‖RO beta hbeta.le‖ ^ 2) *
          (inner ℝ fO (OmegaO beta hbeta.le)) ^ 2 +
        ‖((SO beta hbeta.le) ^ (n + 1)) fO -
          (inner ℝ fO (OmegaO beta hbeta.le)) • (OmegaO beta hbeta.le)‖ ^ 2 -
        ‖RO beta hbeta.le‖ ^ 2 *
          ‖((SO beta hbeta.le) ^ n) fO -
            (inner ℝ fO (OmegaO beta hbeta.le)) • (OmegaO beta hbeta.le)‖ ^ 2 :=
        hLarge
      _ ≤
        (1 - ‖RO beta hbeta.le‖ ^ 2) *
          (inner ℝ fO (OmegaO beta hbeta.le)) ^ 2 +
        (1 - ‖RO beta hbeta.le‖ ^ 2) *
          ‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ^ 2 := by
        linarith
      _ = _ := by ring
  have hStrict := mul_lt_mul_of_pos_left hSmall hCoef
  exact (not_lt_of_ge hUpper) hStrict

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

/-! AJO: audit ALL six new declarations with the actual fixed Lean kernel. -/
#print axioms MGAP4D.MathlibAnalytic.realHilbert_fullTop_power_tail_step_norm_le_ajo
#print axioms MGAP4D.MathlibAnalytic.realHilbert_fullTop_power_tail_step_sq_le_ajo
#print axioms MGAP4D.MathlibAnalytic.realHilbert_selectedPower_sq_twoStep_bracket_ajo
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJO_originalSource_twoStep_selected_sq_bracket
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJO_originalSource_nextPower_sq_budget_implies_excitation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJO_originalSource_twoStep_sq_budget_obstruction
