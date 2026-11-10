import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPowerSelectedTopResidualLimitV5_PZ37AJL
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AJM — finite-power two-sided tests and a genuine AJA obstruction

The ORIGINAL finite-volume SU(2) Wilson normalized one-slab transfer,
physical Haar constant c, centered signed ZW source f₀, chosen unit top
vector Ω, entire fixed top eigenspace F, projection Q, and orthogonal
restriction R are unchanged.

AJK proved the upper residual bound using genuine powers. AJL identified
the exact n→∞ selected-direction residual limits. This leaf proves the
opposite finite-power inequality, hence certified TWO-SIDED error bands
for the two independent original residuals.

Crucially, only the genuine SOURCE extra-top residual rᶠ is proven below
the entire source-top norm. A numerical finite-power source witness can
thus obstruct the STRICT original AJA full-top-small antecedent. This is
conditional on an explicit measured lower bound, not a claim that it
occurs. The HAAR-CONSTANT residual is separately retained; its bound
cannot automatically be promoted to a source-side AJA obstruction.

No change to physical definitions or assumptions; no rank-one top,
vanishing residual, numerical AJA witness, H-uniform gap or continuum
Yang–Mills mass-gap claim.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open Filter
open scoped InnerProductSpace Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- A genuine finite transfer power cannot exceed the selected full-top
residual by more than the proven actual orthogonal power tail. This
direction complements AJK's reverse inequality. -/
theorem realHilbert_selectedPowerDeviation_norm_le_extraTop_add_tail_ajm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E)
    [(realHilbertTopEigenspace S).HasOrthogonalProjection]
    (hSymm : (S : E →ₗ[ℝ] E).IsSymmetric)
    (n : ℕ) (hn : 0 < n) (x omega : E) :
    ‖(S ^ n) x - (inner ℝ x omega) • omega‖ ≤
      ‖(realHilbertTopEigenspace S).starProjection x -
        (inner ℝ x omega) • omega‖ +
      ‖realHilbertTopEigenspaceOrthogonalRestriction S hSymm‖ ^ n *
        ‖((realHilbertTopEigenspace S)ᗮ).starProjection x‖ := by
  let F := realHilbertTopEigenspace S
  let R := realHilbertTopEigenspaceOrthogonalRestriction S hSymm
  have hPower :
      ‖(S ^ n) x - F.starProjection x‖ ≤
        ‖R‖ ^ n * ‖(Fᗮ).starProjection x‖ :=
    realHilbert_fullTop_power_sub_projection_norm_le_aji S hSymm n hn x
  have hTriangle :
      ‖(S ^ n) x - (inner ℝ x omega) • omega‖ ≤
        ‖F.starProjection x - (inner ℝ x omega) • omega‖ +
        ‖(S ^ n) x - F.starProjection x‖ := by
    let a : E := (inner ℝ x omega) • omega
    change ‖(S ^ n) x - a‖ ≤
      ‖F.starProjection x - a‖ + ‖(S ^ n) x - F.starProjection x‖
    have heq :
        (S ^ n) x - a =
          (F.starProjection x - a) + ((S ^ n) x - F.starProjection x) := by
      abel
    rw [heq]
    exact norm_add_le _ _
  exact hTriangle.trans (add_le_add_right hPower _)

/-- At every actual positive finite power, the unknown extra-top
residual is certified within a symmetric additive power-tail band.
This does NOT assert that either residual or tail is numerically small. -/
theorem realHilbert_selectedPowerDeviation_norm_twoSided_ajm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E)
    [(realHilbertTopEigenspace S).HasOrthogonalProjection]
    (hSymm : (S : E →ₗ[ℝ] E).IsSymmetric)
    (n : ℕ) (hn : 0 < n) (x omega : E) :
    (‖(S ^ n) x - (inner ℝ x omega) • omega‖ ≤
      ‖(realHilbertTopEigenspace S).starProjection x -
        (inner ℝ x omega) • omega‖ +
      ‖realHilbertTopEigenspaceOrthogonalRestriction S hSymm‖ ^ n *
        ‖((realHilbertTopEigenspace S)ᗮ).starProjection x‖) ∧
    (‖(realHilbertTopEigenspace S).starProjection x -
        (inner ℝ x omega) • omega‖ ≤
      ‖(S ^ n) x - (inner ℝ x omega) • omega‖ +
      ‖realHilbertTopEigenspaceOrthogonalRestriction S hSymm‖ ^ n *
        ‖((realHilbertTopEigenspace S)ᗮ).starProjection x‖) := by
  exact ⟨
    realHilbert_selectedPowerDeviation_norm_le_extraTop_add_tail_ajm
      S hSymm n hn x omega,
    realHilbert_extraTop_norm_le_finitePower_ajk
      S hSymm n hn x omega⟩

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "PhysM" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "CfgM" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muM" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "fM" =>
  p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "cM" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
local notation "TopM" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace H 2 (by norm_num)
local notation "OmegaM" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector H 2 (by norm_num)
local notation "SM" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "RM" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator H 2 (by norm_num)
local notation "uM" => p4Q2PZ37AIW_originalNormalizedSourceTransfer H
local notation "mM" => p4Q2PZ37AIW_originalNormalizedNegativeMargin H

local instance p4Q2PZ37AJM_physicalComplete (K : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule K 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    K 2).completeSpace_coe

/-- The unchanged genuine Haar constant gets a TWO-SIDED finite-power
error band. Its tail uses its own actual (I-S)c Wilson defect and
finite-H spectral-separation denominator. -/
theorem p4Q2PZ37AJM_originalHaarConstant_powerDeviation_twoSided
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ) (hn : 0 < n) :
    (‖((SM beta hbeta.le) ^ n) cM -
        (inner ℝ cM (OmegaM beta hbeta.le)) • (OmegaM beta hbeta.le)‖ ≤
      ‖p4Q2PZ37AJJ_originalHaarConstantExtraTopComponent H beta hbeta‖ +
      ‖RM beta hbeta.le‖ ^ n *
        (‖cM - (SM beta hbeta.le) cM‖ /
          (1 - ‖RM beta hbeta.le‖))) ∧
    (‖p4Q2PZ37AJJ_originalHaarConstantExtraTopComponent H beta hbeta‖ ≤
      ‖((SM beta hbeta.le) ^ n) cM -
        (inner ℝ cM (OmegaM beta hbeta.le)) • (OmegaM beta hbeta.le)‖ +
      ‖RM beta hbeta.le‖ ^ n *
        (‖cM - (SM beta hbeta.le) cM‖ /
          (1 - ‖RM beta hbeta.le‖))) := by
  let S : PhysM →L[ℝ] PhysM := SM beta hbeta.le
  let hS : (S : PhysM →ₗ[ℝ] PhysM).IsSymmetric :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H 2 (by norm_num) beta hbeta.le
  let F : Submodule ℝ PhysM := realHilbertTopEigenspace S
  let R := realHilbertTopEigenspaceOrthogonalRestriction S hS
  letI : CompleteSpace F :=
    (realHilbertTopEigenspace_isClosed S).completeSpace_coe
  have hGap : ‖R‖ < 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
      H 2 (by norm_num) beta hbeta.le
  change
    (‖(S ^ n) cM -
        (inner ℝ cM (OmegaM beta hbeta.le)) • (OmegaM beta hbeta.le)‖ ≤
      ‖F.starProjection cM -
        (inner ℝ cM (OmegaM beta hbeta.le)) • (OmegaM beta hbeta.le)‖ +
      ‖R‖ ^ n * (‖cM - S cM‖ / (1 - ‖R‖))) ∧
    (‖F.starProjection cM -
        (inner ℝ cM (OmegaM beta hbeta.le)) • (OmegaM beta hbeta.le)‖ ≤
      ‖(S ^ n) cM -
        (inner ℝ cM (OmegaM beta hbeta.le)) • (OmegaM beta hbeta.le)‖ +
      ‖R‖ ^ n * (‖cM - S cM‖ / (1 - ‖R‖)))
  have hTwo :=
    realHilbert_selectedPowerDeviation_norm_twoSided_ajm
      S hS n hn cM (OmegaM beta hbeta.le)
  have hDef :
      ‖(Fᗮ).starProjection cM‖ ≤
        ‖cM - S cM‖ / (1 - ‖R‖) :=
    realHilbert_fullTop_distance_le_defect_div_gap_ajj S hS hGap cM
  have hTail :
      ‖R‖ ^ n * ‖(Fᗮ).starProjection cM‖ ≤
        ‖R‖ ^ n * (‖cM - S cM‖ / (1 - ‖R‖)) :=
    mul_le_mul_of_nonneg_left hDef (pow_nonneg (norm_nonneg R) n)
  exact ⟨
    hTwo.1.trans (add_le_add_right hTail _),
    hTwo.2.trans (add_le_add_right hTail _)⟩

/-- The independent ORIGINAL signed centered ZW source gets its own
two-sided error band with the actual orthogonal-source power tail,
not the Haar-constant defect tail. -/
theorem p4Q2PZ37AJM_originalSource_powerDeviation_twoSided
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ) (hn : 0 < n) :
    (‖((SM beta hbeta.le) ^ n) fM -
        (inner ℝ fM (OmegaM beta hbeta.le)) • (OmegaM beta hbeta.le)‖ ≤
      ‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ +
      ‖RM beta hbeta.le‖ ^ n *
        ‖((TopM beta hbeta.le)ᗮ).starProjection fM‖) ∧
    (‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ≤
      ‖((SM beta hbeta.le) ^ n) fM -
        (inner ℝ fM (OmegaM beta hbeta.le)) • (OmegaM beta hbeta.le)‖ +
      ‖RM beta hbeta.le‖ ^ n *
        ‖((TopM beta hbeta.le)ᗮ).starProjection fM‖) := by
  let S : PhysM →L[ℝ] PhysM := SM beta hbeta.le
  let hS : (S : PhysM →ₗ[ℝ] PhysM).IsSymmetric :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H 2 (by norm_num) beta hbeta.le
  let F : Submodule ℝ PhysM := realHilbertTopEigenspace S
  letI : CompleteSpace F :=
    (realHilbertTopEigenspace_isClosed S).completeSpace_coe
  change
    (‖(S ^ n) fM -
        (inner ℝ fM (OmegaM beta hbeta.le)) • (OmegaM beta hbeta.le)‖ ≤
      ‖F.starProjection fM -
        (inner ℝ fM (OmegaM beta hbeta.le)) • (OmegaM beta hbeta.le)‖ +
      ‖realHilbertTopEigenspaceOrthogonalRestriction S hS‖ ^ n *
        ‖(Fᗮ).starProjection fM‖) ∧
    (‖F.starProjection fM -
        (inner ℝ fM (OmegaM beta hbeta.le)) • (OmegaM beta hbeta.le)‖ ≤
      ‖(S ^ n) fM -
        (inner ℝ fM (OmegaM beta hbeta.le)) • (OmegaM beta hbeta.le)‖ +
      ‖realHilbertTopEigenspaceOrthogonalRestriction S hS‖ ^ n *
        ‖(Fᗮ).starProjection fM‖)
  exact realHilbert_selectedPowerDeviation_norm_twoSided_ajm
    S hS n hn fM (OmegaM beta hbeta.le)

/-- The true source's EXTRA top residual is BELOW its entire top
projection by the exact AJF Pythagoras decomposition. This is the key
direction required for an honest AJA necessary condition. -/
theorem p4Q2PZ37AJM_originalSourceExtraTop_sq_le_fullTop_sq
    (beta : ℝ) (hbeta : 0 < beta) :
    ‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ^ 2 ≤
      ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 := by
  have hSplit :=
    p4Q2PZ37AJF_originalSourceTop_norm_sq_eq_selected_add_extra H beta hbeta
  have hNonneg :
      0 ≤ (inner ℝ fM (OmegaM beta hbeta.le)) ^ 2 := sq_nonneg _
  linarith

/-- A large genuine extra-top SOURCE residual NECESSARILY obstructs the
actual full-top-small premise used by the original AJA certificate.
It does NOT say that this lower bound has actually been observed, or
that the orthogonal excitation must be zero. -/
theorem p4Q2PZ37AJM_originalSourceExtraTop_blocks_fullTopSmall
    (beta : ℝ) (hbeta : 0 < beta)
    (hLarge :
      (mM beta hbeta.le) ^ 2 *
        Measure.real muM
          {B : CfgM | uM beta hbeta.le B < -(mM beta hbeta.le)} ≤
      ‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ^ 2) :
    ¬ (‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 <
      (mM beta hbeta.le) ^ 2 *
        Measure.real muM
          {B : CfgM | uM beta hbeta.le B < -(mM beta hbeta.le)}) := by
  have hLower :=
    hLarge.trans
      (p4Q2PZ37AJM_originalSourceExtraTop_sq_le_fullTop_sq H beta hbeta)
  exact not_lt_of_ge hLower

/-- A single measured genuine finite-power SOURCE deviation can rule out
the strict original full-top-small AJA premise IF an independently
supplied nonnegative threshold fits below that deviation after the
ACTUAL finite-volume tail, and its square exhausts the AJA lower budget.

The threshold and observation are explicit UNPROVEN conditions. No
existence, uniformity, or numerical threshold is manufactured. -/
theorem p4Q2PZ37AJM_originalSourceFinitePower_blocks_fullTopSmall
    (beta : ℝ) (hbeta : 0 < beta)
    (n : ℕ) (hn : 0 < n)
    (threshold : ℝ) (hThreshold : 0 ≤ threshold)
    (hBudget :
      (mM beta hbeta.le) ^ 2 *
        Measure.real muM
          {B : CfgM | uM beta hbeta.le B < -(mM beta hbeta.le)} ≤
        threshold ^ 2)
    (hObserved :
      threshold +
        ‖RM beta hbeta.le‖ ^ n *
          ‖((TopM beta hbeta.le)ᗮ).starProjection fM‖ ≤
        ‖((SM beta hbeta.le) ^ n) fM -
          (inner ℝ fM (OmegaM beta hbeta.le)) •
            (OmegaM beta hbeta.le)‖) :
    ¬ (‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 <
      (mM beta hbeta.le) ^ 2 *
        Measure.real muM
          {B : CfgM | uM beta hbeta.le B < -(mM beta hbeta.le)}) := by
  have hUpper :=
    (p4Q2PZ37AJM_originalSource_powerDeviation_twoSided
      H beta hbeta n hn).1
  have hResidual :
      threshold ≤
        ‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ := by
    linarith
  have hSq :
      threshold ^ 2 ≤
        ‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ^ 2 := by
    have hMul :=
      mul_nonneg (sub_nonneg.mpr hResidual)
        (add_nonneg hThreshold
          (norm_nonneg
            (p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta)))
    nlinarith
  exact
    p4Q2PZ37AJM_originalSourceExtraTop_blocks_fullTopSmall H beta hbeta
      (hBudget.trans hSq)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

/-! Direct kernel axiom inspection of EVERY new theorem. -/
#print axioms MGAP4D.MathlibAnalytic.realHilbert_selectedPowerDeviation_norm_le_extraTop_add_tail_ajm
#print axioms MGAP4D.MathlibAnalytic.realHilbert_selectedPowerDeviation_norm_twoSided_ajm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJM_originalHaarConstant_powerDeviation_twoSided
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJM_originalSource_powerDeviation_twoSided
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJM_originalSourceExtraTop_sq_le_fullTop_sq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJM_originalSourceExtraTop_blocks_fullTopSmall
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJM_originalSourceFinitePower_blocks_fullTopSmall
