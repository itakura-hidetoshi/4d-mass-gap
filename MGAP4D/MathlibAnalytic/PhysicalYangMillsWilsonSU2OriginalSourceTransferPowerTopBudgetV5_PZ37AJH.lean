import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSourceConstantVacuumDeviationV5_PZ37AJG
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AJH — original Wilson transfer powers and two top obstructions

The actual complete SU(2) Wilson one-slab physical transfer, its normalization,
original centered ZW source, physical Haar constant, and the entire original
top eigenspace remain unchanged. The operator is already positive, symmetric,
compact, and has norm one; the full-top orthogonal restriction is strictly
contractive at each finite H without a volume-uniform estimate.

For every natural power, symmetry and the actual fixed-point property imply
that the complete top projection of the UNMODIFIED source is preserved.
Consequently, the full-top source norm and AJF's extra-top residual receive
genuine, directly operator-dependent upper bounds from the iterated source
image. This is a useful independent route around the need to estimate
both AJG contributions separately.

Conversely, the selected top vector's deviation from the Haar constant
has an operator-derived LOWER bound from the loss of the norm of the
transferred constant. It does not provide the desired UPPER bound.
Neither top simplicity nor the required strict Haar-budget comparison is
proved here, and the n=1 full-norm budget cannot beat AJA's existing
lower bound. Any n>=2 strict budget is an additional still-unproved
certificate, not a new standing physical assumption.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- The canonical projection onto a genuine symmetric fixed subspace is
invariant under EVERY natural operator power. This holds for the complete
fixed eigenspace, not an arbitrarily chosen unit eigenvector line. -/
theorem realHilbert_symmetric_fixedSubspace_starProjection_power_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : Submodule ℝ E) [F.HasOrthogonalProjection]
    (S : E →L[ℝ] E)
    (hSymm : (S : E →ₗ[ℝ] E).IsSymmetric)
    (hFix : ∀ v : E, v ∈ F → S v = v)
    (n : ℕ) (x : E) :
    F.starProjection ((S ^ n) x) = F.starProjection x := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        F.starProjection ((S ^ (n + 1)) x) =
            F.starProjection (S ((S ^ n) x)) := by
              rw [pow_succ', ContinuousLinearMap.mul_apply]
        _ = F.starProjection ((S ^ n) x) :=
          realHilbert_symmetric_fixedSubspace_starProjection_eq
            F S hSymm hFix ((S ^ n) x)
        _ = F.starProjection x := ih

/-- The exact original full-fixed projection is controlled by the
physical norm of any genuine iterated transfer image. -/
theorem realHilbert_symmetric_fixedSubspace_projection_norm_sq_le_power
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : Submodule ℝ E) [F.HasOrthogonalProjection]
    (S : E →L[ℝ] E)
    (hSymm : (S : E →ₗ[ℝ] E).IsSymmetric)
    (hFix : ∀ v : E, v ∈ F → S v = v)
    (n : ℕ) (x : E) :
    ‖F.starProjection x‖ ^ 2 ≤ ‖(S ^ n) x‖ ^ 2 := by
  have hproj :=
    realHilbert_symmetric_fixedSubspace_starProjection_power_eq
      F S hSymm hFix n x
  have hbound : ‖F.starProjection x‖ ≤ ‖(S ^ n) x‖ := by
    calc
      ‖F.starProjection x‖ = ‖F.starProjection ((S ^ n) x)‖ := by
        rw [hproj]
      _ ≤ ‖(S ^ n) x‖ := F.norm_starProjection_apply_le _
  have hplus :
      0 ≤ ‖(S ^ n) x‖ + ‖F.starProjection x‖ :=
    add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hmul :=
    mul_nonneg (sub_nonneg.mpr hbound) hplus
  nlinarith

/-- Every actual fixed direction has identical source overlap before
and after any power of the same symmetric operator. -/
theorem realHilbert_symmetric_fixedSubspace_power_inner_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : Submodule ℝ E) [F.HasOrthogonalProjection]
    (S : E →L[ℝ] E)
    (hSymm : (S : E →ₗ[ℝ] E).IsSymmetric)
    (hFix : ∀ v : E, v ∈ F → S v = v)
    (n : ℕ) (x omega : E) (homega : omega ∈ F) :
    inner ℝ ((S ^ n) x) omega = inner ℝ x omega := by
  calc
    inner ℝ ((S ^ n) x) omega =
        inner ℝ (F.starProjection ((S ^ n) x)) omega :=
      realHilbert_starProjection_inner_eq_of_mem F ((S ^ n) x) omega homega
    _ = inner ℝ (F.starProjection x) omega := by
      rw [realHilbert_symmetric_fixedSubspace_starProjection_power_eq
        F S hSymm hFix n x]
    _ = inner ℝ x omega :=
      (realHilbert_starProjection_inner_eq_of_mem F x omega homega).symm

/-- A selected unit fixed vector cannot be CLOSER to a unit constant
than the loss of the constant's true transfer-power norm permits.
This direction is an obstruction/necessary test, not upper control. -/
theorem realHilbert_fixedUnit_deviation_ge_transferPower_norm_deficit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : Submodule ℝ E) [F.HasOrthogonalProjection]
    (S : E →L[ℝ] E)
    (hSymm : (S : E →ₗ[ℝ] E).IsSymmetric)
    (hFix : ∀ v : E, v ∈ F → S v = v)
    (n : ℕ) (c omega : E) (homega : omega ∈ F)
    (homegaUnit : ‖omega‖ = 1) :
    1 - ‖(S ^ n) c‖ ^ 2 ≤
      1 - (inner ℝ omega c) ^ 2 := by
  have hp :=
    realHilbert_symmetric_fixedSubspace_power_inner_eq
      F S hSymm hFix n c omega homega
  have hcs :=
    abs_real_inner_le_norm ((S ^ n) c) omega
  rw [homegaUnit, mul_one, hp, real_inner_comm] at hcs
  have hsq :
      |inner ℝ omega c| ^ 2 ≤ ‖(S ^ n) c‖ ^ 2 := by
    have hnonneg :
        0 ≤ |inner ℝ omega c| + ‖(S ^ n) c‖ :=
      add_nonneg (abs_nonneg _) (norm_nonneg _)
    nlinarith [mul_nonneg (sub_nonneg.mpr hcs) hnonneg]
  have hsq' :
      (inner ℝ omega c) ^ 2 ≤ ‖(S ^ n) c‖ ^ 2 := by
    simpa only [sq_abs] using hsq
  linarith

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "PhysH" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "CfgH" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "fH" =>
  p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "cH" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
local notation "TopH" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace H 2 (by norm_num)
local notation "OmegaH" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector H 2 (by norm_num)
local notation "SH" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "uH" => p4Q2PZ37AIW_originalNormalizedSourceTransfer H
local notation "mH" => p4Q2PZ37AIW_originalNormalizedNegativeMargin H

local instance p4Q2PZ37AJH_physicalComplete (K : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule K 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    K 2).completeSpace_coe

local instance p4Q2PZ37AJH_topComplete
    (K : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
        K 2 (by norm_num) beta hbeta) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_isClosed
    K 2 (by norm_num) beta hbeta).completeSpace_coe

/-- The true original full-top source projection is exactly that of
EVERY iterated original normalized Wilson transfer image. -/
theorem p4Q2PZ37AJH_originalSourceTop_eq_transferPowerTop
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ) :
    (TopH beta hbeta.le).starProjection ((SH beta hbeta.le ^ n) fH) =
      p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta := by
  change (TopH beta hbeta.le).starProjection ((SH beta hbeta.le ^ n) fH) =
    (TopH beta hbeta.le).starProjection fH
  exact realHilbert_symmetric_fixedSubspace_starProjection_power_eq
    (TopH beta hbeta.le) (SH beta hbeta.le)
    (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H 2 (by norm_num) beta hbeta.le)
    (by
      intro v hv
      exact (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_mem
        H 2 (by norm_num) beta hbeta.le v).mp hv)
    n fH

/-- Genuine finite-H,beta transfer-power upper bound for the WHOLE original
top source projection, with no vacuum-line or rank-one reduction. -/
theorem p4Q2PZ37AJH_originalFullTop_norm_sq_le_transferPower
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ) :
    ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 ≤
      ‖((SH beta hbeta.le) ^ n) fH‖ ^ 2 := by
  change ‖(TopH beta hbeta.le).starProjection fH‖ ^ 2 ≤
    ‖((SH beta hbeta.le) ^ n) fH‖ ^ 2
  exact realHilbert_symmetric_fixedSubspace_projection_norm_sq_le_power
    (TopH beta hbeta.le) (SH beta hbeta.le)
    (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H 2 (by norm_num) beta hbeta.le)
    (by
      intro v hv
      exact (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_mem
        H 2 (by norm_num) beta hbeta.le v).mp hv)
    n fH

/-- Operator-based NECESSARY test for a small selected vacuum deviation.
An actual norm loss of the transferred constant LOWER-bounds deviation.
It cannot, by itself, establish the small-deviation side of AJG's budget. -/
theorem p4Q2PZ37AJH_selectedVacuum_deviation_ge_constantPowerNormLoss
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ) :
    1 - ‖((SH beta hbeta.le) ^ n) cH‖ ^ 2 ≤
      1 - (inner ℝ (OmegaH beta hbeta.le) cH) ^ 2 := by
  exact realHilbert_fixedUnit_deviation_ge_transferPower_norm_deficit
    (TopH beta hbeta.le) (SH beta hbeta.le)
    (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H 2 (by norm_num) beta hbeta.le)
    (by
      intro v hv
      exact (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_mem
        H 2 (by norm_num) beta hbeta.le v).mp hv)
    n cH (OmegaH beta hbeta.le)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_mem_topEigenspace
      H 2 (by norm_num) beta hbeta.le)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_norm
      H 2 (by norm_num) beta hbeta.le)

/-- The AJF EXTRA full-top residual is bounded by the SAME ORIGINAL
Wilson transfer power with the actual selected top component removed.
This is an operator-dependent upper bound, not a claim of vanishing. -/
theorem p4Q2PZ37AJH_extraTop_norm_sq_le_transferPower_selectedResidual
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ) :
    ‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ^ 2 ≤
      ‖((SH beta hbeta.le) ^ n) fH -
        (inner ℝ fH (OmegaH beta hbeta.le)) •
          (OmegaH beta hbeta.le)‖ ^ 2 := by
  have htop :=
    p4Q2PZ37AJH_originalFullTop_norm_sq_le_transferPower H beta hbeta n
  have hselected :
      inner ℝ (((SH beta hbeta.le) ^ n) fH) (OmegaH beta hbeta.le) =
        inner ℝ fH (OmegaH beta hbeta.le) := by
    exact realHilbert_symmetric_fixedSubspace_power_inner_eq
      (TopH beta hbeta.le) (SH beta hbeta.le)
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
        H 2 (by norm_num) beta hbeta.le)
      (by
        intro v hv
        exact (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_mem
          H 2 (by norm_num) beta hbeta.le v).mp hv)
      n fH (OmegaH beta hbeta.le)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_mem_topEigenspace
        H 2 (by norm_num) beta hbeta.le)
  have hpower :
      ‖((SH beta hbeta.le) ^ n) fH‖ ^ 2 =
        (inner ℝ fH (OmegaH beta hbeta.le)) ^ 2 +
        ‖((SH beta hbeta.le) ^ n) fH -
          (inner ℝ fH (OmegaH beta hbeta.le)) •
            (OmegaH beta hbeta.le)‖ ^ 2 := by
    simpa only [hselected] using
      (realHilbert_unitDirection_norm_sq_split
        (((SH beta hbeta.le) ^ n) fH)
        (OmegaH beta hbeta.le)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_norm
          H 2 (by norm_num) beta hbeta.le))
  have hsplit :=
    p4Q2PZ37AJF_originalSourceTop_norm_sq_eq_selected_add_extra
      H beta hbeta
  linarith

/-- An independent STRICT upper witness for an actual iterated Wilson
source norm below the existing positive AJA certificate would suffice.
No such witness is asserted, and the power n=1 cannot meet the condition
because AJA already lower-bounds that same norm. -/
theorem p4Q2PZ37AJH_originalOrthogonal_ne_zero_of_transferPower_budget
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ)
    (hPowerBudget :
      ‖((SH beta hbeta.le) ^ n) fH‖ ^ 2 <
        (mH beta hbeta.le) ^ 2 *
          Measure.real muH
            {B : CfgH | uH beta hbeta.le B < -(mH beta hbeta.le)}) :
    p4Q2PZ37AJC_originalNormalizedSourceOrthogonalComponent H beta hbeta ≠ 0 := by
  apply p4Q2PZ37AJD_orthogonal_ne_zero_of_originalSourceTop_small H beta hbeta
  exact lt_of_le_of_lt
    (p4Q2PZ37AJH_originalFullTop_norm_sq_le_transferPower H beta hbeta n)
    hPowerBudget

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

/-! Actual kernel dependency/axiom audit for all new declarations. -/
#print axioms MGAP4D.MathlibAnalytic.realHilbert_symmetric_fixedSubspace_starProjection_power_eq
#print axioms MGAP4D.MathlibAnalytic.realHilbert_symmetric_fixedSubspace_projection_norm_sq_le_power
#print axioms MGAP4D.MathlibAnalytic.realHilbert_symmetric_fixedSubspace_power_inner_eq
#print axioms MGAP4D.MathlibAnalytic.realHilbert_fixedUnit_deviation_ge_transferPower_norm_deficit
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJH_originalSourceTop_eq_transferPowerTop
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJH_originalFullTop_norm_sq_le_transferPower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJH_selectedVacuum_deviation_ge_constantPowerNormLoss
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJH_extraTop_norm_sq_le_transferPower_selectedResidual
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJH_originalOrthogonal_ne_zero_of_transferPower_budget
