import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSourceTransferPowerTopBudgetV5_PZ37AJH
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopEigenspaceDecay
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AJI — exact power-limit test for the original full top budget

The original physical SU(2) Wilson normalized transfer S is positive,
compact, symmetric, norm one, and STRICTLY contractive on the orthogonal
complement of its whole 1-eigenspace at each fixed H,beta. The existing
physical Hilbert carrier, original centered ZW source, and full top
eigenspace/projection are never changed.

All normalized Wilson transfer powers converge geometrically to the
canonical projection on the WHOLE original top eigenspace, without assuming
the top eigenspace is a line. This yields an exact equivalence between the
strict small-full-top budget and existence of a FINITE transfer-power norm
strictly below the ORIGINAL AJA Haar-L2 certificate. The n=1 case is
impossible by AJA itself. No finite witness n, unconditional inequality,
source excitation, uniform-in-volume rate, or continuum mass gap is claimed.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open Filter
open scoped InnerProductSpace Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Natural powers fix every member of an actually fixed subspace, with
no assertion of a rank-one selected vacuum. -/
theorem realHilbert_fixedSubspace_power_fixed_aji
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : Submodule ℝ E) (S : E →L[ℝ] E)
    (hFix : ∀ v : E, v ∈ F → S v = v)
    (n : ℕ) (v : E) (hv : v ∈ F) :
    (S ^ n) v = v := by
  induction n with
  | zero => simp
  | succ n ih =>
      change (S ^ n) (S v) = v
      rw [hFix v hv]
      exact ih

/-- The actual top-orthogonal restriction commutes with its ambient
Wilson transfer powers after the subtype is coerced to the physical space. -/
theorem realHilbert_topOrthogonalRestriction_power_coe_aji
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : E →L[ℝ] E)
    (hSymm : (S : E →ₗ[ℝ] E).IsSymmetric)
    (n : ℕ) (y : (realHilbertTopEigenspace S)ᗮ) :
    (((realHilbertTopEigenspaceOrthogonalRestriction S hSymm ^ n) y :
        (realHilbertTopEigenspace S)ᗮ) : E) =
      (S ^ n) (y : E) := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      change
        (((realHilbertTopEigenspaceOrthogonalRestriction S hSymm ^ n)
          (realHilbertTopEigenspaceOrthogonalRestriction S hSymm y) :
          (realHilbertTopEigenspace S)ᗮ) : E) =
          (S ^ n) (S (y : E))
      rw [ih]
      rw [realHilbertTopEigenspaceOrthogonalRestriction_coe]

/-- Exact finite-power geometric convergence bound in the original real
Hilbert norm, with the WHOLE fixed space and its true orthogonal complement.
The coefficient is the ACTUAL restriction operator norm. -/
theorem realHilbert_fullTop_power_sub_projection_norm_le_aji
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E)
    [(realHilbertTopEigenspace S).HasOrthogonalProjection]
    (hSymm : (S : E →ₗ[ℝ] E).IsSymmetric)
    (n : ℕ) (hn : 0 < n) (x : E) :
    ‖(S ^ n) x - (realHilbertTopEigenspace S).starProjection x‖ ≤
      ‖realHilbertTopEigenspaceOrthogonalRestriction S hSymm‖ ^ n *
        ‖((realHilbertTopEigenspace S)ᗮ).starProjection x‖ := by
  let F := realHilbertTopEigenspace S
  let R := realHilbertTopEigenspaceOrthogonalRestriction S hSymm
  letI : CompleteSpace F :=
    (realHilbertTopEigenspace_isClosed S).completeSpace_coe
  letI : CompleteSpace Fᗮ := F.isClosed_orthogonal.completeSpace_coe
  let t : E := F.starProjection x
  let y : Fᗮ :=
    ⟨(Fᗮ).starProjection x, (Fᗮ).starProjection_apply_mem x⟩
  have hsplit : t + (y : E) = x := by
    exact F.starProjection_add_starProjection_orthogonal x
  have ht : t ∈ F := F.starProjection_apply_mem x
  have hFix : ∀ v : E, v ∈ F → S v = v := by
    intro v hv
    exact (realHilbertTopEigenspace_mem S v).mp hv
  have htop : (S ^ n) t = t :=
    realHilbert_fixedSubspace_power_fixed_aji F S hFix n t ht
  have hcoe :
      (((R ^ n) y : Fᗮ) : E) = (S ^ n) (y : E) :=
    realHilbert_topOrthogonalRestriction_power_coe_aji S hSymm n y
  have hR :
      ‖(R ^ n) y‖ ≤ ‖R‖ ^ n * ‖y‖ := by
    calc
      ‖(R ^ n) y‖ ≤ ‖R ^ n‖ * ‖y‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖R‖ ^ n * ‖y‖ :=
        mul_le_mul_of_nonneg_right (norm_pow_le' R hn) (norm_nonneg y)
  change ‖(S ^ n) x - t‖ ≤ ‖R‖ ^ n * ‖y‖
  calc
    ‖(S ^ n) x - t‖ = ‖(S ^ n) (t + (y : E)) - t‖ := by rw [hsplit]
    _ = ‖(S ^ n) (y : E)‖ := by rw [map_add, htop]; simp
    _ = ‖(R ^ n) y‖ := by rw [← hcoe]; rfl
    _ ≤ ‖R‖ ^ n * ‖y‖ := hR

/-- Genuine full-top power limit for any positive compact norm-one
selfadjoint transfer, assuming only the already proved finite-volume
restriction norm separation < 1. No choice of a vacuum line is made. -/
theorem realHilbert_fullTop_power_succ_tendsto_projection_aji
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E)
    [(realHilbertTopEigenspace S).HasOrthogonalProjection]
    (hSymm : (S : E →ₗ[ℝ] E).IsSymmetric)
    (hq :
      ‖realHilbertTopEigenspaceOrthogonalRestriction S hSymm‖ < 1)
    (x : E) :
    Tendsto (fun n : ℕ => (S ^ (n + 1)) x) atTop
      (nhds ((realHilbertTopEigenspace S).starProjection x)) := by
  let F := realHilbertTopEigenspace S
  let R := realHilbertTopEigenspaceOrthogonalRestriction S hSymm
  letI : CompleteSpace F :=
    (realHilbertTopEigenspace_isClosed S).completeSpace_coe
  letI : CompleteSpace Fᗮ := F.isClosed_orthogonal.completeSpace_coe
  rw [tendsto_iff_dist_tendsto_zero]
  have hq0 : 0 ≤ ‖R‖ := norm_nonneg R
  have hq1 : ‖R‖ ≤ 1 := le_of_lt hq
  have hpow : Tendsto (fun n : ℕ => ‖R‖ ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq
  have hlim :
      Tendsto (fun n : ℕ => ‖R‖ ^ n * ‖(Fᗮ).starProjection x‖)
        atTop (nhds 0) := by
    have hm := hpow.mul
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => ‖(Fᗮ).starProjection x‖) atTop
          (nhds ‖(Fᗮ).starProjection x‖))
    simpa using hm
  have hbound :
      ∀ n : ℕ,
        dist ((S ^ (n + 1)) x) (F.starProjection x) ≤
          ‖R‖ ^ n * ‖(Fᗮ).starProjection x‖ := by
    intro n
    rw [dist_eq_norm]
    have hp :
        ‖(S ^ (n + 1)) x - F.starProjection x‖ ≤
          ‖R‖ ^ (n + 1) * ‖(Fᗮ).starProjection x‖ :=
      realHilbert_fullTop_power_sub_projection_norm_le_aji
        S hSymm (n + 1) (Nat.succ_pos n) x
    have hstep : ‖R‖ ^ (n + 1) ≤ ‖R‖ ^ n := by
      rw [pow_succ]
      nlinarith [mul_nonneg (pow_nonneg hq0 n)
        (sub_nonneg.mpr hq1)]
    exact hp.trans
      (mul_le_mul_of_nonneg_right hstep
        (norm_nonneg ((Fᗮ).starProjection x)))
  exact squeeze_zero (fun _ => dist_nonneg) hbound hlim

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "PhysI" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "CfgI" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muI" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "fI" =>
  p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "TopI" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace H 2 (by norm_num)
local notation "SI" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "RI" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator H 2 (by norm_num)
local notation "uI" => p4Q2PZ37AIW_originalNormalizedSourceTransfer H
local notation "mI" => p4Q2PZ37AIW_originalNormalizedNegativeMargin H

local instance p4Q2PZ37AJI_physicalComplete (K : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule K 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    K 2).completeSpace_coe

local instance p4Q2PZ37AJI_topComplete
    (K : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
        K 2 (by norm_num) beta hbeta) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_isClosed
    K 2 (by norm_num) beta hbeta).completeSpace_coe

/-- Quantitative approach of the actual finite-volume SU(2) Wilson ZW
source power to its WHOLE genuine full-top projection. -/
theorem p4Q2PZ37AJI_originalSource_power_sub_fullTop_norm_le
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ) (hn : 0 < n) :
    ‖((SI beta hbeta.le) ^ n) fI -
      p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ≤
      ‖RI beta hbeta.le‖ ^ n *
        ‖((TopI beta hbeta.le)ᗮ).starProjection fI‖ := by
  let S : PhysI →L[ℝ] PhysI := SI beta hbeta.le
  let hS : (S : PhysI →ₗ[ℝ] PhysI).IsSymmetric :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H 2 (by norm_num) beta hbeta.le
  let F : Submodule ℝ PhysI := realHilbertTopEigenspace S
  let R := realHilbertTopEigenspaceOrthogonalRestriction S hS
  letI : CompleteSpace F :=
    (realHilbertTopEigenspace_isClosed S).completeSpace_coe
  letI : CompleteSpace Fᗮ := F.isClosed_orthogonal.completeSpace_coe
  change
    ‖(S ^ n) fI - F.starProjection fI‖ ≤
      ‖R‖ ^ n * ‖(Fᗮ).starProjection fI‖
  exact realHilbert_fullTop_power_sub_projection_norm_le_aji
    S hS n hn fI

/-- Fixed finite H,beta: the actual ORIGINAL normalized transfer powers
converge in the true physical Hilbert norm to the complete full-top
source projection, not a substitute rank-one vacuum projection. -/
theorem p4Q2PZ37AJI_originalSource_power_succ_tendsto_fullTop
    (beta : ℝ) (hbeta : 0 < beta) :
    Tendsto (fun n : ℕ => ((SI beta hbeta.le) ^ (n + 1)) fI)
      atTop
      (nhds (p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta)) := by
  let S : PhysI →L[ℝ] PhysI := SI beta hbeta.le
  let hS : (S : PhysI →ₗ[ℝ] PhysI).IsSymmetric :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H 2 (by norm_num) beta hbeta.le
  let F : Submodule ℝ PhysI := realHilbertTopEigenspace S
  let R := realHilbertTopEigenspaceOrthogonalRestriction S hS
  letI : CompleteSpace F :=
    (realHilbertTopEigenspace_isClosed S).completeSpace_coe
  letI : CompleteSpace Fᗮ := F.isClosed_orthogonal.completeSpace_coe
  have hR : ‖R‖ < 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
      H 2 (by norm_num) beta hbeta.le
  change
    Tendsto (fun n : ℕ => (S ^ (n + 1)) fI)
      atTop (nhds (F.starProjection fI))
  exact realHilbert_fullTop_power_succ_tendsto_projection_aji
    S hS hR fI

/-- A strict ORIGINAL full-top smallness condition is EQUIVALENT to the
existence of a positive finite power of the same original Wilson transfer
whose genuine source norm falls below the same AJA Haar certificate.
This is a completeness of WITNESS TEST, not an unconditional witness. -/
theorem p4Q2PZ37AJI_fullTop_small_iff_exists_transferPower_budget
    (beta : ℝ) (hbeta : 0 < beta) :
    (‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 <
      (mI beta hbeta.le) ^ 2 *
        Measure.real muI
          {B : CfgI | uI beta hbeta.le B < -(mI beta hbeta.le)}) ↔
    ∃ n : ℕ, 0 < n ∧
      ‖((SI beta hbeta.le) ^ n) fI‖ ^ 2 <
        (mI beta hbeta.le) ^ 2 *
          Measure.real muI
            {B : CfgI | uI beta hbeta.le B < -(mI beta hbeta.le)} := by
  constructor
  · intro hsmall
    have hlim :=
      p4Q2PZ37AJI_originalSource_power_succ_tendsto_fullTop H beta hbeta
    have hlimSq :
        Tendsto
          (fun n : ℕ => ‖((SI beta hbeta.le) ^ (n + 1)) fI‖ ^ 2)
          atTop
          (nhds
            (‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2)) :=
      hlim.norm.pow 2
    have hevent :
        ∀ᶠ n : ℕ in atTop,
          ‖((SI beta hbeta.le) ^ (n + 1)) fI‖ ^ 2 <
            (mI beta hbeta.le) ^ 2 *
              Measure.real muI
                {B : CfgI | uI beta hbeta.le B < -(mI beta hbeta.le)} :=
      hlimSq.eventually (isOpen_Iio.mem_nhds hsmall)
    obtain ⟨n, hn⟩ := hevent.exists
    exact ⟨n + 1, Nat.succ_pos n, hn⟩
  · rintro ⟨n, hn, hsmall⟩
    exact lt_of_le_of_lt
      (p4Q2PZ37AJH_originalFullTop_norm_sq_le_transferPower H beta hbeta n)
      hsmall

/-- The true first power cannot already satisfy the strict AJA
certificate budget; AJA provides a LOWER bound on exactly this norm. -/
theorem p4Q2PZ37AJI_no_firstPower_budget
    (beta : ℝ) (hbeta : 0 < beta) :
    ¬ (‖(SI beta hbeta.le) fI‖ ^ 2 <
      (mI beta hbeta.le) ^ 2 *
        Measure.real muI
          {B : CfgI | uI beta hbeta.le B < -(mI beta hbeta.le)}) := by
  exact not_lt_of_ge
    (p4Q2PZ37AJA_originalNormalizedPhysicalSource_norm_sq_ge_margin_measure
      H beta hbeta)

/-- If a strict genuine finite-power test is independently certified, the
original normalized source has a nonzero projection onto the complete
excitation/orthogonal sector. This does not certify such a power. -/
theorem p4Q2PZ37AJI_originalOrthogonal_ne_zero_of_exists_transferPower_budget
    (beta : ℝ) (hbeta : 0 < beta)
    (hExists :
      ∃ n : ℕ, 0 < n ∧
        ‖((SI beta hbeta.le) ^ n) fI‖ ^ 2 <
          (mI beta hbeta.le) ^ 2 *
            Measure.real muI
              {B : CfgI | uI beta hbeta.le B < -(mI beta hbeta.le)}) :
    p4Q2PZ37AJC_originalNormalizedSourceOrthogonalComponent H beta hbeta ≠ 0 := by
  obtain ⟨n, _hn, hSmall⟩ := hExists
  exact p4Q2PZ37AJH_originalOrthogonal_ne_zero_of_transferPower_budget
    H beta hbeta n hSmall

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

/-! Real kernel axiom outputs for every newly introduced true-code claim. -/
#print axioms MGAP4D.MathlibAnalytic.realHilbert_fixedSubspace_power_fixed_aji
#print axioms MGAP4D.MathlibAnalytic.realHilbert_topOrthogonalRestriction_power_coe_aji
#print axioms MGAP4D.MathlibAnalytic.realHilbert_fullTop_power_sub_projection_norm_le_aji
#print axioms MGAP4D.MathlibAnalytic.realHilbert_fullTop_power_succ_tendsto_projection_aji
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJI_originalSource_power_sub_fullTop_norm_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJI_originalSource_power_succ_tendsto_fullTop
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJI_fullTop_small_iff_exists_transferPower_budget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJI_no_firstPower_budget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJI_originalOrthogonal_ne_zero_of_exists_transferPower_budget
