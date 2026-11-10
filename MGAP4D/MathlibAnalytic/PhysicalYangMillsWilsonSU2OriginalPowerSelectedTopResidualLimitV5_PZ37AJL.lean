import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFinitePowerIndependentTopResidualsV5_PZ37AJK
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AJL — exact finite-power asymptotics of two original top residuals

The original normalized SU(2) Wilson transfer powers converge to the
WHOLE top projection at each fixed finite H and positive beta (AJI).
After removing a selected unit top vector, their genuine physical norms
therefore converge to the corresponding separately defined EXTRA-TOP
residual norms, for both the original Haar constant and original centered
ZW source.

Consequently, increasing the transfer power alone does NOT force these
two independent residuals to vanish. No unknown strict AJA Haar-L2 budget,
rank-one vacuum, H-uniform spectral coercivity, or continuum mass gap
is inferred from finite-volume convergence.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- At a fixed finite-volume spectral separation, the original transfer's
selected-direction power deviation has an EXACT limit equal to the full
top-projection selected-direction residual. No rank-one assumption. -/
theorem realHilbert_selectedPowerDeviation_norm_tendsto_ajl
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E)
    [(realHilbertTopEigenspace S).HasOrthogonalProjection]
    (hSymm : (S : E →ₗ[ℝ] E).IsSymmetric)
    (hq : ‖realHilbertTopEigenspaceOrthogonalRestriction S hSymm‖ < 1)
    (x omega : E) :
    Tendsto
      (fun n : ℕ => ‖(S ^ (n + 1)) x - (inner ℝ x omega) • omega‖)
      atTop
      (nhds
        ‖(realHilbertTopEigenspace S).starProjection x -
          (inner ℝ x omega) • omega‖) := by
  have hlim :
      Tendsto (fun n : ℕ => (S ^ (n + 1)) x) atTop
        (nhds ((realHilbertTopEigenspace S).starProjection x)) :=
    realHilbert_fullTop_power_succ_tendsto_projection_aji S hSymm hq x
  have hconst :
      Tendsto (fun _ : ℕ => (inner ℝ x omega) • omega) atTop
        (nhds ((inner ℝ x omega) • omega)) :=
    tendsto_const_nhds
  exact (hlim.sub hconst).norm

/-- The nonnegative squared selected-direction finite-power discrepancy
also converges to the squared whole-top extra residual, rather than to
zero unless a separate residual-vanishing theorem is supplied. -/
theorem realHilbert_selectedPowerDeviation_sq_tendsto_ajl
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E)
    [(realHilbertTopEigenspace S).HasOrthogonalProjection]
    (hSymm : (S : E →ₗ[ℝ] E).IsSymmetric)
    (hq : ‖realHilbertTopEigenspaceOrthogonalRestriction S hSymm‖ < 1)
    (x omega : E) :
    Tendsto
      (fun n : ℕ => ‖(S ^ (n + 1)) x - (inner ℝ x omega) • omega‖ ^ 2)
      atTop
      (nhds
        (‖(realHilbertTopEigenspace S).starProjection x -
          (inner ℝ x omega) • omega‖ ^ 2)) := by
  exact (realHilbert_selectedPowerDeviation_norm_tendsto_ajl
    S hSymm hq x omega).pow 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "PhysL" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "fL" =>
  p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "cL" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
local notation "OmegaL" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector H 2 (by norm_num)
local notation "SL" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator H 2 (by norm_num)

local instance p4Q2PZ37AJL_physicalComplete (K : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule K 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    K 2).completeSpace_coe

/-- The genuine Haar constant's selected-top finite-power discrepancy
converges to AJJ's previously defined constant-side extra-top residual. -/
theorem p4Q2PZ37AJL_originalHaarConstant_powerDeviation_norm_tendsto
    (beta : ℝ) (hbeta : 0 < beta) :
    Tendsto
      (fun n : ℕ =>
        ‖((SL beta hbeta.le) ^ (n + 1)) cL -
          (inner ℝ cL (OmegaL beta hbeta.le)) • (OmegaL beta hbeta.le)‖)
      atTop
      (nhds
        ‖p4Q2PZ37AJJ_originalHaarConstantExtraTopComponent H beta hbeta‖) := by
  let S : PhysL →L[ℝ] PhysL := SL beta hbeta.le
  let hS : (S : PhysL →ₗ[ℝ] PhysL).IsSymmetric :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H 2 (by norm_num) beta hbeta.le
  let F : Submodule ℝ PhysL := realHilbertTopEigenspace S
  letI : CompleteSpace F :=
    (realHilbertTopEigenspace_isClosed S).completeSpace_coe
  have hR : ‖realHilbertTopEigenspaceOrthogonalRestriction S hS‖ < 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
      H 2 (by norm_num) beta hbeta.le
  change
    Tendsto
      (fun n : ℕ =>
        ‖(S ^ (n + 1)) cL -
          (inner ℝ cL (OmegaL beta hbeta.le)) • (OmegaL beta hbeta.le)‖)
      atTop
      (nhds
        ‖F.starProjection cL -
          (inner ℝ cL (OmegaL beta hbeta.le)) • (OmegaL beta hbeta.le)‖)
  exact realHilbert_selectedPowerDeviation_norm_tendsto_ajl
    S hS hR cL (OmegaL beta hbeta.le)

/-- The genuine signed centered ZW source's finite-power discrepancy
converges to the distinct AJF source-side extra-top residual, not AJJ's
constant-side residual. -/
theorem p4Q2PZ37AJL_originalSource_powerDeviation_norm_tendsto
    (beta : ℝ) (hbeta : 0 < beta) :
    Tendsto
      (fun n : ℕ =>
        ‖((SL beta hbeta.le) ^ (n + 1)) fL -
          (inner ℝ fL (OmegaL beta hbeta.le)) • (OmegaL beta hbeta.le)‖)
      atTop
      (nhds
        ‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖) := by
  let S : PhysL →L[ℝ] PhysL := SL beta hbeta.le
  let hS : (S : PhysL →ₗ[ℝ] PhysL).IsSymmetric :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H 2 (by norm_num) beta hbeta.le
  let F : Submodule ℝ PhysL := realHilbertTopEigenspace S
  letI : CompleteSpace F :=
    (realHilbertTopEigenspace_isClosed S).completeSpace_coe
  have hR : ‖realHilbertTopEigenspaceOrthogonalRestriction S hS‖ < 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
      H 2 (by norm_num) beta hbeta.le
  change
    Tendsto
      (fun n : ℕ =>
        ‖(S ^ (n + 1)) fL -
          (inner ℝ fL (OmegaL beta hbeta.le)) • (OmegaL beta hbeta.le)‖)
      atTop
      (nhds
        ‖F.starProjection fL -
          (inner ℝ fL (OmegaL beta hbeta.le)) • (OmegaL beta hbeta.le)‖)
  exact realHilbert_selectedPowerDeviation_norm_tendsto_ajl
    S hS hR fL (OmegaL beta hbeta.le)

/-- Both actual finite-power test sequences have rigorous square-norm
limits, leaving the extra-top constant residual quantitatively visible. -/
theorem p4Q2PZ37AJL_originalHaarConstant_powerDeviation_sq_tendsto
    (beta : ℝ) (hbeta : 0 < beta) :
    Tendsto
      (fun n : ℕ =>
        ‖((SL beta hbeta.le) ^ (n + 1)) cL -
          (inner ℝ cL (OmegaL beta hbeta.le)) • (OmegaL beta hbeta.le)‖ ^ 2)
      atTop
      (nhds
        (‖p4Q2PZ37AJJ_originalHaarConstantExtraTopComponent H beta hbeta‖ ^ 2)) := by
  exact
    (p4Q2PZ37AJL_originalHaarConstant_powerDeviation_norm_tendsto
      H beta hbeta).pow 2

/-- The corresponding genuine ZW source square-norm limit keeps the
independent AJF extra-top residual as an explicit obstruction. -/
theorem p4Q2PZ37AJL_originalSource_powerDeviation_sq_tendsto
    (beta : ℝ) (hbeta : 0 < beta) :
    Tendsto
      (fun n : ℕ =>
        ‖((SL beta hbeta.le) ^ (n + 1)) fL -
          (inner ℝ fL (OmegaL beta hbeta.le)) • (OmegaL beta hbeta.le)‖ ^ 2)
      atTop
      (nhds
        (‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ^ 2)) := by
  exact
    (p4Q2PZ37AJL_originalSource_powerDeviation_norm_tendsto
      H beta hbeta).pow 2

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

/-! Direct kernel axiom inspection for all six new declarations. -/
#print axioms MGAP4D.MathlibAnalytic.realHilbert_selectedPowerDeviation_norm_tendsto_ajl
#print axioms MGAP4D.MathlibAnalytic.realHilbert_selectedPowerDeviation_sq_tendsto_ajl
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJL_originalHaarConstant_powerDeviation_norm_tendsto
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJL_originalSource_powerDeviation_norm_tendsto
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJL_originalHaarConstant_powerDeviation_sq_tendsto
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJL_originalSource_powerDeviation_sq_tendsto
