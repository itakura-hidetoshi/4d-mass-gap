import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalJointRealFeatureCrossingV5_KH
import Mathlib.Tactic

/-!
# P4-Q2-KJ — SU(2) real feature is genuinely injective and original joint
# density separates EVERY pair of distinct SU(2) inserted link values

KH identifies the actual original interacting Wilson/Perron joint-density
four-corner cross ratio with the exponential of a REAL finite-dimensional
matrix-feature inner product. This file proves without any rank hypothesis
that the same matrix realification is injective, by recovering every
complex matrix entry's real and imaginary coordinates. Therefore for
any distinct physical SU(2) link values g,h and any b>0, choosing the
two actual left configurations with link values g,h makes the original
Wilson/Perron joint 2x2 minor STRICTLY positive.

This is all-pairs pointwise strict total positivity at genuine Wilson
left and right link insertions, not an assertion of integral-transform
injectivity or physical GI detector separation. No new axiom, sorry,
independent Haar posterior, Dobrushin, H1-C3 or continuum mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Actual complex-matrix realification detects every individual matrix
entry; it is a theorem-proved injective map, not an imposed rank
condition on the original Wilson detector. -/
theorem p4Q2KJ_complexMatrixRealFeature_injective (N : ℕ) :
    Function.Injective (complexMatrixRealFeature N) := by
  intro A B h
  apply Matrix.ext
  intro i j
  apply Complex.ext
  · have hre := congrArg
      (fun v : SpecialUnitaryMatrixRealFeatureSpace N => v ((j,i), true)) h
    simpa [complexMatrixRealFeature] using hre
  · have him := congrArg
      (fun v : SpecialUnitaryMatrixRealFeatureSpace N => v ((j,i), false)) h
    simpa [complexMatrixRealFeature] using him

/-- The concrete real Hilbert feature of genuine SU(N) group matrices
is injective, since the underlying complex matrix is recovered from
the finite real/imaginary coordinate feature. -/
theorem p4Q2KJ_specialUnitaryMatrixRealFeature_injective (N : ℕ) :
    Function.Injective (specialUnitaryMatrixRealFeature N) := by
  intro u v h
  apply Subtype.ext
  exact p4Q2KJ_complexMatrixRealFeature_injective N h

namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Phi" => specialUnitaryMatrixRealFeature 2
local notation "rho" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight
    H 2 (by norm_num)

/-- Genuine SU(2) real-feature separation makes the EXPONENTIAL of
its own squared feature difference strictly greater than one for
every distinct actual link pair and each positive coupling. -/
theorem p4Q2KJ_exp_realFeatureSquaredDifference_gt_one
    (b : ℝ) (hb : 0 < b) (g h : Gauge) (hne : g ≠ h) :
    1 < Real.exp ((b / 2) *
      inner ℝ (Phi g - Phi h) (Phi g - Phi h)) := by
  have hPhi : Phi g ≠ Phi h := by
    intro heq
    exact hne ((p4Q2KJ_specialUnitaryMatrixRealFeature_injective 2) heq)
  have hDiff : Phi g - Phi h ≠ 0 := sub_ne_zero.mpr hPhi
  have hNorm : 0 < ‖Phi g - Phi h‖ := norm_pos_iff.mpr hDiff
  have hInner : 0 < inner ℝ (Phi g - Phi h) (Phi g - Phi h) := by
    rw [real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos hNorm
  have hCoeff : 0 < b / 2 := by positivity
  exact Real.one_lt_exp_iff.mpr (mul_pos hCoeff hInner)

/-- The authentic Wilson/Perron joint four-point determinant is
strictly positive at ANY pair g != h when the two actual physical
left boundaries are chosen with link values g and h respectively.
This holds for every finite volume H, actual spatial link, right
background and frozen positive Wilson coupling, with unchanged joint
normalization and Perron vacuum. -/
theorem p4Q2KJ_originalJoint_anyDistinctSU2_pair_strictDet
    (b : ℝ) (hb : 0 < b) (right : Cfg) (e : Link)
    (g h : Gauge) (hne : g ≠ h) :
    rho b hb.le ((fun _ : Link => g), Function.update right e g) *
      rho b hb.le ((fun _ : Link => h), Function.update right e h) >
    rho b hb.le ((fun _ : Link => g), Function.update right e h) *
      rho b hb.le ((fun _ : Link => h), Function.update right e g) := by
  let Lg : Cfg := fun _ => g
  let Lh : Cfg := fun _ => h
  let Bg : Cfg := Function.update right e g
  let Bh : Cfg := Function.update right e h
  let x : ℝ := rho b hb.le (Lg, Bh) * rho b hb.le (Lh, Bg)
  have hx : 0 < x := mul_pos
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight_pos
      H 2 (by norm_num) b hb.le (Lg, Bh))
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight_pos
      H 2 (by norm_num) b hb.le (Lh, Bg))
  have hFour :=
    p4Q2KH_originalJointFourCorner_eq_realFeatureExponential
      H b hb.le Lg Lh right e g h
  have hExponent : 1 < Real.exp ((b / 2) *
        inner ℝ (Phi g - Phi h) (Phi g - Phi h)) :=
    p4Q2KJ_exp_realFeatureSquaredDifference_gt_one H b hb g h hne
  have hStrict :
      x < Real.exp ((b / 2) *
        inner ℝ (Phi g - Phi h) (Phi g - Phi h)) * x :=
    (lt_mul_iff_one_lt_left hx).2 hExponent
  change rho b hb.le (Lg, Bg) * rho b hb.le (Lh, Bh) > x
  have hIdentity :
      rho b hb.le (Lg, Bg) * rho b hb.le (Lh, Bh) =
        Real.exp ((b / 2) *
          inner ℝ (Phi g - Phi h) (Phi g - Phi h)) * x := by
    simpa only [Lg, Lh, Bg, Bh, x] using hFour
  rw [hIdentity]
  exact hStrict

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.p4Q2KJ_complexMatrixRealFeature_injective
#print axioms MGAP4D.MathlibAnalytic.p4Q2KJ_specialUnitaryMatrixRealFeature_injective
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KJ_exp_realFeatureSquaredDifference_gt_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KJ_originalJoint_anyDistinctSU2_pair_strictDet
