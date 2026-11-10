import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalHaarConstantTopResidualV5_PZ37AJJ
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AJK — independent finite-power witnesses for two extra-top residuals

Use the genuine normalized original SU(2) Wilson transfer, entire original
top eigenspace, Haar constant and centered ZW source. The two extra-top
residuals are not interchangeable and are NOT assumed to vanish.

For arbitrary positive finite n, the selected-direction residual of each
original vector is bounded by its own actual Wilson transfer power plus
the independently certified full-top convergence remainder. The Haar
constant's remainder can in turn be bounded by its original (I-S)c defect
and the genuine finite-volume spectral separation from AJJ.

No finite n is shown to satisfy the strict AJA certificate, and no
unconditional nonzero excitation, top simplicity, H-uniform gap, or
continuum Yang-Mills mass gap is asserted.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- The extra component relative to ANY selected direction has an
independent, finite-power upper bound, with the exact full-top tail.
No rank-one top projection or positivity assumption on the direction. -/
theorem realHilbert_extraTop_norm_le_finitePower_ajk
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E)
    [(realHilbertTopEigenspace S).HasOrthogonalProjection]
    (hSymm : (S : E →ₗ[ℝ] E).IsSymmetric)
    (n : ℕ) (hn : 0 < n) (x omega : E) :
    ‖(realHilbertTopEigenspace S).starProjection x -
      (inner ℝ x omega) • omega‖ ≤
      ‖(S ^ n) x - (inner ℝ x omega) • omega‖ +
        ‖realHilbertTopEigenspaceOrthogonalRestriction S hSymm‖ ^ n *
          ‖((realHilbertTopEigenspace S)ᗮ).starProjection x‖ := by
  let F := realHilbertTopEigenspace S
  let R := realHilbertTopEigenspaceOrthogonalRestriction S hSymm
  have hpower :
      ‖(S ^ n) x - F.starProjection x‖ ≤
        ‖R‖ ^ n * ‖(Fᗮ).starProjection x‖ :=
    realHilbert_fullTop_power_sub_projection_norm_le_aji S hSymm n hn x
  have htriangle :
      ‖F.starProjection x - (inner ℝ x omega) • omega‖ ≤
        ‖(S ^ n) x - (inner ℝ x omega) • omega‖ +
          ‖(S ^ n) x - F.starProjection x‖ := by
    let a : E := (inner ℝ x omega) • omega
    change ‖F.starProjection x - a‖ ≤
      ‖(S ^ n) x - a‖ + ‖(S ^ n) x - F.starProjection x‖
    have heq :
        F.starProjection x - a =
          ((S ^ n) x - a) + -((S ^ n) x - F.starProjection x) := by
      abel
    rw [heq]
    simpa only [norm_neg] using
      (norm_add_le ((S ^ n) x - a) (-((S ^ n) x - F.starProjection x)))
  exact htriangle.trans (add_le_add_left hpower _)

/-- AJJ additionally controls the selected-direction constant residual
by a finite ORIGINAL transfer power plus a defect-dependent tail. The
positive denominator follows from the already proven finite-volume gap. -/
theorem realHilbert_extraTop_norm_le_finitePower_defect_ajk
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E)
    [(realHilbertTopEigenspace S).HasOrthogonalProjection]
    (hSymm : (S : E →ₗ[ℝ] E).IsSymmetric)
    (hq : ‖realHilbertTopEigenspaceOrthogonalRestriction S hSymm‖ < 1)
    (n : ℕ) (hn : 0 < n) (c omega : E) :
    ‖(realHilbertTopEigenspace S).starProjection c -
      (inner ℝ c omega) • omega‖ ≤
      ‖(S ^ n) c - (inner ℝ c omega) • omega‖ +
        ‖realHilbertTopEigenspaceOrthogonalRestriction S hSymm‖ ^ n *
          (‖c - S c‖ /
            (1 - ‖realHilbertTopEigenspaceOrthogonalRestriction S hSymm‖)) := by
  let F := realHilbertTopEigenspace S
  let R := realHilbertTopEigenspaceOrthogonalRestriction S hSymm
  have hpow :
      ‖F.starProjection c - (inner ℝ c omega) • omega‖ ≤
        ‖(S ^ n) c - (inner ℝ c omega) • omega‖ +
          ‖R‖ ^ n * ‖(Fᗮ).starProjection c‖ :=
    realHilbert_extraTop_norm_le_finitePower_ajk S hSymm n hn c omega
  have hdef :
      ‖(Fᗮ).starProjection c‖ ≤ ‖c - S c‖ / (1 - ‖R‖) :=
    realHilbert_fullTop_distance_le_defect_div_gap_ajj S hSymm hq c
  have htail :
      ‖R‖ ^ n * ‖(Fᗮ).starProjection c‖ ≤
        ‖R‖ ^ n * (‖c - S c‖ / (1 - ‖R‖)) :=
    mul_le_mul_of_nonneg_left hdef (pow_nonneg (norm_nonneg R) n)
  exact hpow.trans (add_le_add_left htail _)

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "PhysK" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "fK" =>
  p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "cK" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
local notation "TopK" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace H 2 (by norm_num)
local notation "OmegaK" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector H 2 (by norm_num)
local notation "SK" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "RK" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator H 2 (by norm_num)

local instance p4Q2PZ37AJK_physicalComplete (K : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule K 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    K 2).completeSpace_coe

/-- Genuine Haar constant: a separately testable finite-power bound for
its extra top residual. This does not assume that the Haar constant is
fixed by S or that selected Omega spans the full top eigenspace. -/
theorem p4Q2PZ37AJK_originalHaarConstantExtraTop_norm_le_power_defect
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ) (hn : 0 < n) :
    ‖p4Q2PZ37AJJ_originalHaarConstantExtraTopComponent H beta hbeta‖ ≤
      ‖((SK beta hbeta.le) ^ n) cK -
        (inner ℝ cK (OmegaK beta hbeta.le)) • (OmegaK beta hbeta.le)‖ +
      ‖RK beta hbeta.le‖ ^ n *
        (‖cK - (SK beta hbeta.le) cK‖ /
          (1 - ‖RK beta hbeta.le‖)) := by
  let S : PhysK →L[ℝ] PhysK := SK beta hbeta.le
  let hS : (S : PhysK →ₗ[ℝ] PhysK).IsSymmetric :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H 2 (by norm_num) beta hbeta.le
  let F : Submodule ℝ PhysK := realHilbertTopEigenspace S
  let R := realHilbertTopEigenspaceOrthogonalRestriction S hS
  letI : CompleteSpace F := (realHilbertTopEigenspace_isClosed S).completeSpace_coe
  have hR : ‖R‖ < 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
      H 2 (by norm_num) beta hbeta.le
  change ‖F.starProjection cK -
      (inner ℝ cK (OmegaK beta hbeta.le)) • (OmegaK beta hbeta.le)‖ ≤
    ‖(S ^ n) cK -
      (inner ℝ cK (OmegaK beta hbeta.le)) • (OmegaK beta hbeta.le)‖ +
    ‖R‖ ^ n * (‖cK - S cK‖ / (1 - ‖R‖))
  exact realHilbert_extraTop_norm_le_finitePower_defect_ajk
    S hS hR n hn cK (OmegaK beta hbeta.le)

/-- Genuine centered ZW source: a distinct finite-power bound for AJF's
extra top residual. Its orthogonal-source tail is not confused with
the defect tail of the Haar constant. No strict AJA budget witness. -/
theorem p4Q2PZ37AJK_originalSourceExtraTop_norm_le_power
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ) (hn : 0 < n) :
    ‖p4Q2PZ37AJF_originalSourceExtraTopComponent H beta hbeta‖ ≤
      ‖((SK beta hbeta.le) ^ n) fK -
        (inner ℝ fK (OmegaK beta hbeta.le)) • (OmegaK beta hbeta.le)‖ +
      ‖RK beta hbeta.le‖ ^ n *
        ‖((TopK beta hbeta.le)ᗮ).starProjection fK‖ := by
  let S : PhysK →L[ℝ] PhysK := SK beta hbeta.le
  let hS : (S : PhysK →ₗ[ℝ] PhysK).IsSymmetric :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H 2 (by norm_num) beta hbeta.le
  let F : Submodule ℝ PhysK := realHilbertTopEigenspace S
  let R := realHilbertTopEigenspaceOrthogonalRestriction S hS
  letI : CompleteSpace F := (realHilbertTopEigenspace_isClosed S).completeSpace_coe
  change ‖F.starProjection fK -
      (inner ℝ fK (OmegaK beta hbeta.le)) • (OmegaK beta hbeta.le)‖ ≤
    ‖(S ^ n) fK -
      (inner ℝ fK (OmegaK beta hbeta.le)) • (OmegaK beta hbeta.le)‖ +
    ‖R‖ ^ n * ‖(Fᗮ).starProjection fK‖
  exact realHilbert_extraTop_norm_le_finitePower_ajk
    S hS n hn fK (OmegaK beta hbeta.le)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

/-! Audit every new declaration against the fixed kernel axioms. -/
#print axioms MGAP4D.MathlibAnalytic.realHilbert_extraTop_norm_le_finitePower_ajk
#print axioms MGAP4D.MathlibAnalytic.realHilbert_extraTop_norm_le_finitePower_defect_ajk
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJK_originalHaarConstantExtraTop_norm_le_power_defect
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJK_originalSourceExtraTop_norm_le_power
