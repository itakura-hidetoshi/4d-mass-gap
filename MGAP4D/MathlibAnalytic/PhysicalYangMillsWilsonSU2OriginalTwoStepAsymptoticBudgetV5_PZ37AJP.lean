import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalTwoStepResidualBudgetV5_PZ37AJO
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AJP — asymptotically sharp two-step Wilson residual budget

AJO proved an actual two-consecutive-power bracket on the UNKNOWN extra-top
square of the ORIGINAL signed centered ZW source in the original finite-H
SU(2) Wilson Gauss-law physical Hilbert space. AJP studies the exact
asymptotic meaning of those TWO observed finite-power quantities, retaining
the SAME source, transfer, selected top eigenvector, entire top eigenspace
and genuine orthogonal restriction.

Write q = ‖R‖ < 1 (the EXISTING pointwise finite-H,beta result),
D_n = ‖S^n f₀ - ⟨f₀,Ω⟩Ω‖², and
e² = ‖Q f₀ - ⟨f₀,Ω⟩Ω‖². Then the actual two-step lower estimator

  L_n = (D_(n+2) - q² D_(n+1)) / (1-q²)

satisfies L_n ≤ e² ≤ D_(n+2), and BOTH its endpoints converge to e².
Consequently, strict separation of the full-top square from the unchanged
AJA Haar budget produces eventually verifiable finite two-power tests on
the corresponding side. EQUALITY remains an open boundary, not a numerical
witness or an assumption that the extra-top residual vanishes.

Nothing here establishes a particular numeric witness, rank-one top,
uniform-in-H coercivity, unconditional excitation, a Hamiltonian gap or
the four-dimensional continuum Yang–Mills mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open Filter
open scoped InnerProductSpace Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "PhysP" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "CfgP" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muP" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "fP" =>
  p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "OmegaP" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector H 2 (by norm_num)
local notation "SP" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "RP" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator H 2 (by norm_num)
local notation "uP" => p4Q2PZ37AIW_originalNormalizedSourceTransfer H
local notation "mP" => p4Q2PZ37AIW_originalNormalizedNegativeMargin H

local instance p4Q2PZ37AJP_physicalComplete (K : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule K 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    K 2).completeSpace_coe

local instance p4Q2PZ37AJP_topComplete
    (K : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
        K 2 (by norm_num) beta hbeta) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_isClosed
    K 2 (by norm_num) beta hbeta).completeSpace_coe

/-- Actual finite Wilson source selected-top-subtracted squared norm,
with the ORIGINAL top Ω. No one-dimensional top is postulated. -/
noncomputable def p4Q2PZ37AJP_originalSourceSelectedSquare
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ) : ℝ :=
  ‖((SP beta hbeta.le) ^ n) fP -
    (inner ℝ fP (OmegaP beta hbeta.le)) • (OmegaP beta hbeta.le)‖ ^ 2

/-- True two-adjacent-power posterior lower endpoint. q is the EXISTING
orthogonal Wilson restriction norm, not a fitted or uniform rate. -/
noncomputable def p4Q2PZ37AJP_originalSourceTwoStepLower
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ) : ℝ :=
  (p4Q2PZ37AJP_originalSourceSelectedSquare H beta hbeta (n + 2) -
    ‖RP beta hbeta.le‖ ^ 2 *
      p4Q2PZ37AJP_originalSourceSelectedSquare H beta hbeta (n + 1)) /
    (1 - ‖RP beta hbeta.le‖ ^ 2)

/-- The selected-power square approaches precisely the EXTRA-TOP
square, not zero unless that extra-top component independently vanishes. -/
theorem p4Q2PZ37AJP_originalSource_selectedSquare_succ_tendsto_extra
    (beta : ℝ) (hbeta : 0 < beta) :
    Tendsto
      (fun n : ℕ => p4Q2PZ37AJP_originalSourceSelectedSquare H beta hbeta (n + 1))
      atTop
      (nhds (‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ^ 2)) := by
  have hlim :=
    p4Q2PZ37AJI_originalSource_power_succ_tendsto_fullTop H beta hbeta
  have hdiff :
      Tendsto
        (fun n : ℕ =>
          ((SP beta hbeta.le) ^ (n + 1)) fP -
            (inner ℝ fP (OmegaP beta hbeta.le)) • (OmegaP beta hbeta.le))
        atTop
        (nhds
          (p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta -
            (inner ℝ fP (OmegaP beta hbeta.le)) • (OmegaP beta hbeta.le))) :=
    hlim.sub tendsto_const_nhds
  change Tendsto
    (fun n : ℕ =>
      ‖((SP beta hbeta.le) ^ (n + 1)) fP -
        (inner ℝ fP (OmegaP beta hbeta.le)) • (OmegaP beta hbeta.le)‖ ^ 2)
    atTop
    (nhds
      (‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta -
        (inner ℝ fP (OmegaP beta hbeta.le)) • (OmegaP beta hbeta.le)‖ ^ 2))
  exact hdiff.norm.pow 2

/-- AJO's genuine two-power posterior interval at all n≥0. The
denominator is strictly positive by the OLD physical finite-volume
restriction norm inequality. -/
theorem p4Q2PZ37AJP_originalSource_twoStep_posterior_interval
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ) :
    (p4Q2PZ37AJP_originalSourceTwoStepLower H beta hbeta n ≤
      ‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ^ 2) ∧
    (‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ^ 2 ≤
      p4Q2PZ37AJP_originalSourceSelectedSquare H beta hbeta (n + 2)) := by
  have hbracket :=
    p4Q2PZ37AJO_originalSource_twoStep_selected_sq_bracket
      H beta hbeta (n + 1)
  have hR : ‖RP beta hbeta.le‖ < 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
      H 2 (by norm_num) beta hbeta.le
  have hcoef : 0 < 1 - ‖RP beta hbeta.le‖ ^ 2 := by
    have hnonneg : 0 ≤ ‖RP beta hbeta.le‖ := norm_nonneg (RP beta hbeta.le)
    nlinarith
  let S : PhysP →L[ℝ] PhysP := SP beta hbeta.le
  let omega : PhysP := OmegaP beta hbeta.le
  let R := RP beta hbeta.le
  constructor
  · unfold p4Q2PZ37AJP_originalSourceTwoStepLower
    apply (div_le_iff₀ hcoef).2
    change
      ‖(S ^ (n + 2)) fP - (inner ℝ fP omega) • omega‖ ^ 2 -
          ‖R‖ ^ 2 * ‖(S ^ (n + 1)) fP -
            (inner ℝ fP omega) • omega‖ ^ 2 ≤
        ‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ^ 2 *
          (1 - ‖R‖ ^ 2)
    calc
      _ ≤ (1 - ‖R‖ ^ 2) *
        ‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ^ 2 :=
          hbracket.1
      _ = _ := by ring
  · change
      ‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ^ 2 ≤
        ‖(S ^ (n + 2)) fP - (inner ℝ fP omega) • omega‖ ^ 2
    exact hbracket.2

/-- Unlike an independent numerical witness, this is an exact limiting
IDENTIFICATION: the lower two-step endpoint converges to the same
original extra-top square as the upper endpoint. -/
theorem p4Q2PZ37AJP_originalSource_twoStepLower_tendsto_extra
    (beta : ℝ) (hbeta : 0 < beta) :
    Tendsto
      (fun n : ℕ => p4Q2PZ37AJP_originalSourceTwoStepLower H beta hbeta n)
      atTop
      (nhds (‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ^ 2)) := by
  let q : ℝ := ‖RP beta hbeta.le‖
  let r2 : ℝ := ‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ^ 2
  have hR : q < 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
      H 2 (by norm_num) beta hbeta.le
  have hcoef : 0 < 1 - q ^ 2 := by
    have hnonneg : 0 ≤ q := norm_nonneg (RP beta hbeta.le)
    nlinarith
  have hneq : 1 - q ^ 2 ≠ 0 := ne_of_gt hcoef
  have hlim :
      Tendsto
        (fun n : ℕ =>
          p4Q2PZ37AJP_originalSourceSelectedSquare H beta hbeta (n + 1))
        atTop (nhds r2) :=
    p4Q2PZ37AJP_originalSource_selectedSquare_succ_tendsto_extra H beta hbeta
  have hlim2 :
      Tendsto
        (fun n : ℕ =>
          p4Q2PZ37AJP_originalSourceSelectedSquare H beta hbeta (n + 2))
        atTop (nhds r2) := by
    simpa [Nat.add_assoc] using
      (hlim.comp (tendsto_add_atTop_nat 1))
  have hmul :
      Tendsto
        (fun n : ℕ =>
          q ^ 2 * p4Q2PZ37AJP_originalSourceSelectedSquare H beta hbeta (n + 1))
        atTop (nhds (q ^ 2 * r2)) :=
    tendsto_const_nhds.mul hlim
  have hnum :
      Tendsto
        (fun n : ℕ =>
          p4Q2PZ37AJP_originalSourceSelectedSquare H beta hbeta (n + 2) -
          q ^ 2 * p4Q2PZ37AJP_originalSourceSelectedSquare H beta hbeta (n + 1))
        atTop (nhds (r2 - q ^ 2 * r2)) :=
    hlim2.sub hmul
  have hident : (r2 - q ^ 2 * r2) / (1 - q ^ 2) = r2 := by
    apply (div_eq_iff hneq).2
    ring
  have hdiv := hnum.div_const (1 - q ^ 2)
  change Tendsto
    (fun n : ℕ =>
      (p4Q2PZ37AJP_originalSourceSelectedSquare H beta hbeta (n + 2) -
        q ^ 2 * p4Q2PZ37AJP_originalSourceSelectedSquare H beta hbeta (n + 1)) /
        (1 - q ^ 2))
    atTop (nhds r2)
  simpa only [hident] using hdiv

/-- If actual full-top mass is STRICTLY below the unchanged Haar
certificate, eventually the UPPER endpoint of the two-step posterior
gives a sufficient finite-power AJA test. No n is asserted unconditionally. -/
theorem p4Q2PZ37AJP_originalSource_strictSmall_eventually_upperBudget
    (beta : ℝ) (hbeta : 0 < beta)
    (hSmall :
      ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 <
        (mP beta hbeta.le) ^ 2 *
          Measure.real muP
            {B : CfgP | uP beta hbeta.le B < -(mP beta hbeta.le)}) :
    ∀ᶠ n : ℕ in atTop,
      (inner ℝ fP (OmegaP beta hbeta.le)) ^ 2 +
        p4Q2PZ37AJP_originalSourceSelectedSquare H beta hbeta (n + 2) <
      (mP beta hbeta.le) ^ 2 *
        Measure.real muP
          {B : CfgP | uP beta hbeta.le B < -(mP beta hbeta.le)} := by
  have hlim :=
    p4Q2PZ37AJP_originalSource_selectedSquare_succ_tendsto_extra H beta hbeta
  have hlim2 :
      Tendsto
        (fun n : ℕ =>
          p4Q2PZ37AJP_originalSourceSelectedSquare H beta hbeta (n + 2))
        atTop
        (nhds (‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ^ 2)) := by
    simpa [Nat.add_assoc] using
      (hlim.comp (tendsto_add_atTop_nat 1))
  have hsum :
      Tendsto
        (fun n : ℕ =>
          (inner ℝ fP (OmegaP beta hbeta.le)) ^ 2 +
            p4Q2PZ37AJP_originalSourceSelectedSquare H beta hbeta (n + 2))
        atTop
        (nhds
          ((inner ℝ fP (OmegaP beta hbeta.le)) ^ 2 +
            ‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ^ 2)) :=
    tendsto_const_nhds.add hlim2
  rw [p4Q2PZ37AJF_originalSourceTop_norm_sq_eq_selected_add_extra
    H beta hbeta] at hSmall
  exact hsum.eventually (isOpen_Iio.mem_nhds hSmall)

/-- If genuine full-top mass is STRICTLY above the Haar certificate,
the LOWER two-step endpoint eventually gives a finite negative budget
diagnostic. The exact equality boundary is not decided by this theorem. -/
theorem p4Q2PZ37AJP_originalSource_strictLarge_eventually_lowerObstruction
    (beta : ℝ) (hbeta : 0 < beta)
    (hLarge :
      (mP beta hbeta.le) ^ 2 *
        Measure.real muP
          {B : CfgP | uP beta hbeta.le B < -(mP beta hbeta.le)} <
      ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2) :
    ∀ᶠ n : ℕ in atTop,
      (mP beta hbeta.le) ^ 2 *
        Measure.real muP
          {B : CfgP | uP beta hbeta.le B < -(mP beta hbeta.le)} <
      (inner ℝ fP (OmegaP beta hbeta.le)) ^ 2 +
        p4Q2PZ37AJP_originalSourceTwoStepLower H beta hbeta n := by
  have hlim :=
    p4Q2PZ37AJP_originalSource_twoStepLower_tendsto_extra H beta hbeta
  have hsum :
      Tendsto
        (fun n : ℕ =>
          (inner ℝ fP (OmegaP beta hbeta.le)) ^ 2 +
            p4Q2PZ37AJP_originalSourceTwoStepLower H beta hbeta n)
        atTop
        (nhds
          ((inner ℝ fP (OmegaP beta hbeta.le)) ^ 2 +
            ‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ^ 2)) :=
    tendsto_const_nhds.add hlim
  rw [p4Q2PZ37AJF_originalSourceTop_norm_sq_eq_selected_add_extra
    H beta hbeta] at hLarge
  exact hsum.eventually (isOpen_Ioi.mem_nhds hLarge)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

/-! AJP: audit both definitions and all five theorems on the fixed Lean kernel. -/
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJP_originalSourceSelectedSquare
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJP_originalSourceTwoStepLower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJP_originalSource_selectedSquare_succ_tendsto_extra
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJP_originalSource_twoStep_posterior_interval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJP_originalSource_twoStepLower_tendsto_extra
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJP_originalSource_strictSmall_eventually_upperBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJP_originalSource_strictLarge_eventually_lowerObstruction
