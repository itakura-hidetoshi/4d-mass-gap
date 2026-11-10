import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFinitePowerTopBudgetObstructionV5_PZ37AJM
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AJN — exact orthogonal square split for original Wilson powers

AJM's valid but nonsharp triangle-norm bands are upgraded WITHOUT
additional physical assumptions. For a symmetric transfer fixing the
entire closed top space F, the selected-vacuum-subtracted power is the
orthogonal sum of an EXTRA-TOP residual and a true power-decay vector.

This yields the exact squared Pythagorean identity and a one-sided,
nonnegative geometric square remainder. Both original physical vectors,
Haar c and signed centered ZW f₀, are specialized separately.

For the original source, the same finite-power measurement now gives
both a sufficient strict AJA full-top-small test and a necessary no-go
test, with an explicit unresolved square-tail interval. No numerical
witness, rank-one top, residual vanishing, H-uniform gap, unconditional
excitation or continuum 4D Yang-Mills mass gap is asserted.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open Filter
open scoped InnerProductSpace Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Exact Pythagoras: for a symmetric transfer whose full fixed
subspace is F, the chosen-direction residual and the decaying
top-orthogonal power are orthogonal, not merely triangle-bounded. -/
theorem realHilbert_fixedSubspace_selectedPower_sq_split_ajn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : Submodule ℝ E) [F.HasOrthogonalProjection]
    (S : E →L[ℝ] E)
    (hSymm : (S : E →ₗ[ℝ] E).IsSymmetric)
    (hFix : ∀ v : E, v ∈ F → S v = v)
    (n : ℕ) (x omega : E) (homega : omega ∈ F) :
    ‖(S ^ n) x - (inner ℝ x omega) • omega‖ ^ 2 =
      ‖F.starProjection x - (inner ℝ x omega) • omega‖ ^ 2 +
      ‖(S ^ n) x - F.starProjection x‖ ^ 2 := by
  let a : E := F.starProjection x - (inner ℝ x omega) • omega
  let b : E := (S ^ n) x - F.starProjection x
  have ha : a ∈ F :=
    F.sub_mem (F.starProjection_apply_mem x) (F.smul_mem _ homega)
  have hCross : inner ℝ a b = 0 := by
    calc
      inner ℝ a b = inner ℝ b a := (real_inner_comm a b).symm
      _ = inner ℝ ((S ^ n) x) a - inner ℝ (F.starProjection x) a := by
        dsimp [b]
        rw [inner_sub_left]
      _ = inner ℝ x a - inner ℝ x a := by
        rw [realHilbert_symmetric_fixedSubspace_power_inner_eq
          F S hSymm hFix n x a ha]
        rw [(realHilbert_starProjection_inner_eq_of_mem F x a ha).symm]
      _ = 0 := sub_self _
  have hSum :
      (S ^ n) x - (inner ℝ x omega) • omega = a + b := by
    dsimp [a, b]
    abel
  rw [hSum, norm_add_sq_real, hCross]
  ring

/-- The gap-controlled nonnegative square remainder is sharper than
the AJM absolute-norm triangle band. No smallness of the top residual
is inferred; the residual is bounded by the observed power squared. -/
theorem realHilbert_fullTop_selectedPower_sq_interval_ajn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E)
    [(realHilbertTopEigenspace S).HasOrthogonalProjection]
    (hSymm : (S : E →ₗ[ℝ] E).IsSymmetric)
    (n : ℕ) (hn : 0 < n) (x omega : E)
    (homega : omega ∈ realHilbertTopEigenspace S) :
    (‖(realHilbertTopEigenspace S).starProjection x -
        (inner ℝ x omega) • omega‖ ^ 2 ≤
      ‖(S ^ n) x - (inner ℝ x omega) • omega‖ ^ 2) ∧
    (‖(S ^ n) x - (inner ℝ x omega) • omega‖ ^ 2 ≤
      ‖(realHilbertTopEigenspace S).starProjection x -
        (inner ℝ x omega) • omega‖ ^ 2 +
      (‖realHilbertTopEigenspaceOrthogonalRestriction S hSymm‖ ^ n *
        ‖((realHilbertTopEigenspace S)ᗮ).starProjection x‖) ^ 2) := by
  let F := realHilbertTopEigenspace S
  let R := realHilbertTopEigenspaceOrthogonalRestriction S hSymm
  letI : CompleteSpace F := (realHilbertTopEigenspace_isClosed S).completeSpace_coe
  have hFix : ∀ v : E, v ∈ F → S v = v := by
    intro v hv
    exact (realHilbertTopEigenspace_mem S v).mp hv
  have hSplit :
      ‖(S ^ n) x - (inner ℝ x omega) • omega‖ ^ 2 =
        ‖F.starProjection x - (inner ℝ x omega) • omega‖ ^ 2 +
        ‖(S ^ n) x - F.starProjection x‖ ^ 2 :=
    realHilbert_fixedSubspace_selectedPower_sq_split_ajn
      F S hSymm hFix n x omega homega
  have hTail :
      ‖(S ^ n) x - F.starProjection x‖ ≤
        ‖R‖ ^ n * ‖(Fᗮ).starProjection x‖ :=
    realHilbert_fullTop_power_sub_projection_norm_le_aji
      S hSymm n hn x
  have hTailNonneg :
      0 ≤ ‖R‖ ^ n * ‖(Fᗮ).starProjection x‖ :=
    mul_nonneg (pow_nonneg (norm_nonneg R) n)
      (norm_nonneg ((Fᗮ).starProjection x))
  have hTailSq :
      ‖(S ^ n) x - F.starProjection x‖ ^ 2 ≤
        (‖R‖ ^ n * ‖(Fᗮ).starProjection x‖) ^ 2 := by
    have hMul :=
      mul_nonneg (sub_nonneg.mpr hTail)
        (add_nonneg (norm_nonneg ((S ^ n) x - F.starProjection x)) hTailNonneg)
    nlinarith
  constructor
  · rw [hSplit]
    exact le_add_of_nonneg_right (sq_nonneg _)
  · rw [hSplit]
    exact add_le_add_right hTailSq _

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "PhysN" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "CfgN" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muN" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "fN" =>
  p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "cN" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
local notation "TopN" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace H 2 (by norm_num)
local notation "OmegaN" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector H 2 (by norm_num)
local notation "SN" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "RN" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator H 2 (by norm_num)
local notation "uN" => p4Q2PZ37AIW_originalNormalizedSourceTransfer H
local notation "mN" => p4Q2PZ37AIW_originalNormalizedNegativeMargin H

local instance p4Q2PZ37AJN_physicalComplete (K : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule K 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    K 2).completeSpace_coe

/-- The unchanged original finite-H top space is closed, hence complete,
and thus admits the fixed-mathlib orthogonal projection. -/
local instance p4Q2PZ37AJN_topComplete
    (K : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
        K 2 (by norm_num) beta hbeta) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_isClosed
    K 2 (by norm_num) beta hbeta).completeSpace_coe

/-- ORIGINAL Haar constant; exact squared finite-power Pythagoras, with
its own extra-top residual and genuine orthogonal Wilson power. -/
theorem p4Q2PZ37AJN_originalHaarConstant_powerDeviation_sq_eq_extra_add_orth
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ) :
    ‖((SN beta hbeta.le) ^ n) cN -
      (inner ℝ cN (OmegaN beta hbeta.le)) • (OmegaN beta hbeta.le)‖ ^ 2 =
      ‖p4Q2PZ37AJJ_originalHaarConstantExtraTopComponent H beta hbeta‖ ^ 2 +
      ‖((SN beta hbeta.le) ^ n) cN -
        (TopN beta hbeta.le).starProjection cN‖ ^ 2 := by
  let S : PhysN →L[ℝ] PhysN := SN beta hbeta.le
  let F : Submodule ℝ PhysN := realHilbertTopEigenspace S
  let hS : (S : PhysN →ₗ[ℝ] PhysN).IsSymmetric :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H 2 (by norm_num) beta hbeta.le
  letI : CompleteSpace F :=
    (realHilbertTopEigenspace_isClosed S).completeSpace_coe
  have hFix : ∀ v : PhysN, v ∈ F → S v = v := by
    intro v hv
    exact (realHilbertTopEigenspace_mem S v).mp hv
  change
    ‖(S ^ n) cN -
      (inner ℝ cN (OmegaN beta hbeta.le)) • (OmegaN beta hbeta.le)‖ ^ 2 =
      ‖F.starProjection cN -
        (inner ℝ cN (OmegaN beta hbeta.le)) • (OmegaN beta hbeta.le)‖ ^ 2 +
      ‖(S ^ n) cN - F.starProjection cN‖ ^ 2
  exact realHilbert_fixedSubspace_selectedPower_sq_split_ajn
    F S hS hFix n cN (OmegaN beta hbeta.le)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_mem_topEigenspace
      H 2 (by norm_num) beta hbeta.le)

/-- ORIGINAL signed centered ZW source; exact squared Pythagoras with
the DIFFERENT source-side AJF extra-top residual. -/
theorem p4Q2PZ37AJN_originalSource_powerDeviation_sq_eq_extra_add_orth
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ) :
    ‖((SN beta hbeta.le) ^ n) fN -
      (inner ℝ fN (OmegaN beta hbeta.le)) • (OmegaN beta hbeta.le)‖ ^ 2 =
      ‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ^ 2 +
      ‖((SN beta hbeta.le) ^ n) fN -
        (TopN beta hbeta.le).starProjection fN‖ ^ 2 := by
  let S : PhysN →L[ℝ] PhysN := SN beta hbeta.le
  let F : Submodule ℝ PhysN := realHilbertTopEigenspace S
  let hS : (S : PhysN →ₗ[ℝ] PhysN).IsSymmetric :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H 2 (by norm_num) beta hbeta.le
  letI : CompleteSpace F :=
    (realHilbertTopEigenspace_isClosed S).completeSpace_coe
  have hFix : ∀ v : PhysN, v ∈ F → S v = v := by
    intro v hv
    exact (realHilbertTopEigenspace_mem S v).mp hv
  change
    ‖(S ^ n) fN -
      (inner ℝ fN (OmegaN beta hbeta.le)) • (OmegaN beta hbeta.le)‖ ^ 2 =
      ‖F.starProjection fN -
        (inner ℝ fN (OmegaN beta hbeta.le)) • (OmegaN beta hbeta.le)‖ ^ 2 +
      ‖(S ^ n) fN - F.starProjection fN‖ ^ 2
  exact realHilbert_fixedSubspace_selectedPower_sq_split_ajn
    F S hS hFix n fN (OmegaN beta hbeta.le)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_mem_topEigenspace
      H 2 (by norm_num) beta hbeta.le)

/-- Physical SOURCE square-power interval, with a one-sided nonnegative
geometric square tail. This is stronger than AJM's triangle band. -/
theorem p4Q2PZ37AJN_originalSource_powerDeviation_sq_interval
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ) (hn : 0 < n) :
    (‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ^ 2 ≤
      ‖((SN beta hbeta.le) ^ n) fN -
        (inner ℝ fN (OmegaN beta hbeta.le)) • (OmegaN beta hbeta.le)‖ ^ 2) ∧
    (‖((SN beta hbeta.le) ^ n) fN -
        (inner ℝ fN (OmegaN beta hbeta.le)) • (OmegaN beta hbeta.le)‖ ^ 2 ≤
      ‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ^ 2 +
        (‖RN beta hbeta.le‖ ^ n *
          ‖((TopN beta hbeta.le)ᗮ).starProjection fN‖) ^ 2) := by
  let S : PhysN →L[ℝ] PhysN := SN beta hbeta.le
  let F : Submodule ℝ PhysN := realHilbertTopEigenspace S
  let hS : (S : PhysN →ₗ[ℝ] PhysN).IsSymmetric :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H 2 (by norm_num) beta hbeta.le
  letI : CompleteSpace F :=
    (realHilbertTopEigenspace_isClosed S).completeSpace_coe
  change
    (‖F.starProjection fN -
        (inner ℝ fN (OmegaN beta hbeta.le)) • (OmegaN beta hbeta.le)‖ ^ 2 ≤
      ‖(S ^ n) fN -
        (inner ℝ fN (OmegaN beta hbeta.le)) • (OmegaN beta hbeta.le)‖ ^ 2) ∧
    (‖(S ^ n) fN -
        (inner ℝ fN (OmegaN beta hbeta.le)) • (OmegaN beta hbeta.le)‖ ^ 2 ≤
      ‖F.starProjection fN -
        (inner ℝ fN (OmegaN beta hbeta.le)) • (OmegaN beta hbeta.le)‖ ^ 2 +
        (‖realHilbertTopEigenspaceOrthogonalRestriction S hS‖ ^ n *
          ‖(Fᗮ).starProjection fN‖) ^ 2)
  exact realHilbert_fullTop_selectedPower_sq_interval_ajn
    S hS n hn fN (OmegaN beta hbeta.le)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_mem_topEigenspace
      H 2 (by norm_num) beta hbeta.le)

/-- A FINITE original Wilson source selected-deviation square test is
SUFFICIENT for strict original AJA small-full-top and nonzero excitation.
The witness is not provided here (n=1 is known impossible by AJI). -/
theorem p4Q2PZ37AJN_originalSource_selectedPower_sq_budget_implies_excitation
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ)
    (hSmall :
      (inner ℝ fN (OmegaN beta hbeta.le)) ^ 2 +
        ‖((SN beta hbeta.le) ^ n) fN -
          (inner ℝ fN (OmegaN beta hbeta.le)) • (OmegaN beta hbeta.le)‖ ^ 2 <
      (mN beta hbeta.le) ^ 2 *
        Measure.real muN
          {B : CfgN | uN beta hbeta.le B < -(mN beta hbeta.le)}) :
    p4Q2PZ37AJC_originalNormalizedSourceOrthogonalComponent
      H beta hbeta ≠ 0 := by
  have hResidual :=
    p4Q2PZ37AJH_extraTop_norm_sq_le_transferPower_selectedResidual
      H beta hbeta n
  have hFull :=
    p4Q2PZ37AJF_originalSourceTop_norm_sq_eq_selected_add_extra
      H beta hbeta
  apply p4Q2PZ37AJD_orthogonal_ne_zero_of_originalSourceTop_small H beta hbeta
  linarith

/-- Exact certified two-sided test for the strict AJA full-top-small
predicate. A finite source power has selected+residual score dSq.
If the fixed AJA budget is at most dSq minus the certified genuine
decaying square tail, strict smallness is IMPOSSIBLE.
Unlike the triangle threshold in AJM this uses orthogonal Pythagoras.
No claim that this premise has been numerically established. -/
theorem p4Q2PZ37AJN_originalSource_selectedPower_sq_budget_obstruction
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ) (hn : 0 < n)
    (hLarge :
      (mN beta hbeta.le) ^ 2 *
        Measure.real muN
          {B : CfgN | uN beta hbeta.le B < -(mN beta hbeta.le)} +
        (‖RN beta hbeta.le‖ ^ n *
          ‖((TopN beta hbeta.le)ᗮ).starProjection fN‖) ^ 2 ≤
        (inner ℝ fN (OmegaN beta hbeta.le)) ^ 2 +
        ‖((SN beta hbeta.le) ^ n) fN -
          (inner ℝ fN (OmegaN beta hbeta.le)) • (OmegaN beta hbeta.le)‖ ^ 2) :
    ¬ (‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 <
      (mN beta hbeta.le) ^ 2 *
        Measure.real muN
          {B : CfgN | uN beta hbeta.le B < -(mN beta hbeta.le)}) := by
  have hSq :=
    (p4Q2PZ37AJN_originalSource_powerDeviation_sq_interval
      H beta hbeta n hn).2
  have hFull :=
    p4Q2PZ37AJF_originalSourceTop_norm_sq_eq_selected_add_extra H beta hbeta
  intro hSmall
  rw [hFull] at hSmall
  linarith

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

/-! All seven declarations are audited on the fixed kernel. -/
#print axioms MGAP4D.MathlibAnalytic.realHilbert_fixedSubspace_selectedPower_sq_split_ajn
#print axioms MGAP4D.MathlibAnalytic.realHilbert_fullTop_selectedPower_sq_interval_ajn
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJN_originalHaarConstant_powerDeviation_sq_eq_extra_add_orth
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJN_originalSource_powerDeviation_sq_eq_extra_add_orth
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJN_originalSource_powerDeviation_sq_interval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJN_originalSource_selectedPower_sq_budget_implies_excitation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJN_originalSource_selectedPower_sq_budget_obstruction
