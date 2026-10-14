import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalEveryLinkNormalizedPosteriorSensitivityV5_FS
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalConditionalPosteriorDensityFloorV5_FK
import Mathlib.Tactic

/-!
# P4-Q2-FU: volume-uniform positive 2x2 minor of the TRUE Wilson posterior density

FS proves the exact four-corner logarithmic ratio 4*beta at EVERY
original physical spatial link e, with real SU(2) left boundaries
identity and the pi-rotation at e, and right insertions 1 and R(pi).

FK proves the true interacting normalized one-link conditional Wilson
density lies in [exp(-16*beta), exp(16*beta)], uniformly in volume.

Combining those results, the actual normalized conditional density
four-corner matrix P_e (NOT a chosen surrogate kernel) satisfies

  det(P_e) = (exp(4*beta)-1) * P_e[0,1] * P_e[1,0],

and the EXPLICIT volume-independent lower bound

  det(P_e) >= (exp(4*beta)-1) * exp(-32*beta) > 0

at every finite H, every physical link e, every right environment B,
and every fixed positive physical beta.

This is a quantitative pointwise true-posterior crossing certificate.
A positive determinant at two points in an atomless compact Haar group
is NOT BY ITSELF a volume-uniform integrated RMS lower frame; the
remaining left-Haar translation/conditional-distance integration must
still be established. No Dobrushin or continuum Yang--Mills claim.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 650000

namespace GroundStatePosteriorJoint

/-- Generic positive four-corner log ratio determines the EXACT
two-by-two determinant, with no boundedness or probability assumption. -/
theorem p4Q2FU_positiveFourCornerLog_crossing_eq_minor
    (a b c d t : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hCross : (Real.log a - Real.log b) -
        (Real.log c - Real.log d) = t) :
    a * d - b * c = (Real.exp t - 1) * (b * c) := by
  have hLog : Real.log a + Real.log d =
      t + (Real.log b + Real.log c) := by
    linarith [hCross]
  have hExp := congrArg Real.exp hLog
  have hL : Real.exp (Real.log a + Real.log d) = a * d := by
    rw [Real.exp_add, Real.exp_log ha, Real.exp_log hd]
  have hR : Real.exp (t + (Real.log b + Real.log c)) =
      Real.exp t * (b * c) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_log hb, Real.exp_log hc]
  rw [hL, hR] at hExp
  rw [hExp]
  ring

/-- Each entry of the literal SU(2) conditional posterior four-corner
matrix: row false = original left identity, row true = left pi rotation
at physical link e; column false = right value 1, true = R(pi). -/
noncomputable def p4Q2FU_originalSU2WilsonPosteriorFourCornerEntry
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (row col : Bool) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
    H 2 (by norm_num) beta hbeta
    (if row then p4Q2FQ_originalSU2LeftPiRotationAtLink H e
      else originalWilsonExplicitIdentityBoundary H)
    right e
    (if col then specialUnitaryTwoRotation Real.pi
      else (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))

/-- TRUE normalized physical SU(2) Wilson posterior density 2x2 minor
at an arbitrary original physical link and right environment. -/
noncomputable def p4Q2FU_originalSU2WilsonPosteriorFourCornerMinor
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  p4Q2FU_originalSU2WilsonPosteriorFourCornerEntry
      H beta hbeta right e false false *
    p4Q2FU_originalSU2WilsonPosteriorFourCornerEntry
      H beta hbeta right e true true -
  p4Q2FU_originalSU2WilsonPosteriorFourCornerEntry
      H beta hbeta right e false true *
    p4Q2FU_originalSU2WilsonPosteriorFourCornerEntry
      H beta hbeta right e true false

/-- Exact TRUE physical Wilson posterior two-by-two determinant formula
independent of finite spatial volume H. It is not a surrogate minor. -/
theorem p4Q2FU_originalSU2WilsonPosteriorMinor_eq_exact
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    p4Q2FU_originalSU2WilsonPosteriorFourCornerMinor
      H beta hbeta right e =
    (Real.exp (4 * beta) - 1) *
      (p4Q2FU_originalSU2WilsonPosteriorFourCornerEntry
        H beta hbeta right e false true *
       p4Q2FU_originalSU2WilsonPosteriorFourCornerEntry
        H beta hbeta right e true false) := by
  let a := p4Q2FU_originalSU2WilsonPosteriorFourCornerEntry
    H beta hbeta right e false false
  let b := p4Q2FU_originalSU2WilsonPosteriorFourCornerEntry
    H beta hbeta right e false true
  let c := p4Q2FU_originalSU2WilsonPosteriorFourCornerEntry
    H beta hbeta right e true false
  let d := p4Q2FU_originalSU2WilsonPosteriorFourCornerEntry
    H beta hbeta right e true true
  have hLoA : Real.exp (-16 * beta) ≤ a := by
    exact (p4Q2FK_originalWilsonPosteriorConditionalDensity_twoSided
      H 2 (by norm_num) beta hbeta
      (originalWilsonExplicitIdentityBoundary H) right e 1).1
  have hLoB : Real.exp (-16 * beta) ≤ b := by
    exact (p4Q2FK_originalWilsonPosteriorConditionalDensity_twoSided
      H 2 (by norm_num) beta hbeta
      (originalWilsonExplicitIdentityBoundary H) right e
      (specialUnitaryTwoRotation Real.pi)).1
  have hLoC : Real.exp (-16 * beta) ≤ c := by
    exact (p4Q2FK_originalWilsonPosteriorConditionalDensity_twoSided
      H 2 (by norm_num) beta hbeta
      (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e 1).1
  have hLoD : Real.exp (-16 * beta) ≤ d := by
    exact (p4Q2FK_originalWilsonPosteriorConditionalDensity_twoSided
      H 2 (by norm_num) beta hbeta
      (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e
      (specialUnitaryTwoRotation Real.pi)).1
  have ha : 0 < a := (Real.exp_pos _).trans_le hLoA
  have hb : 0 < b := (Real.exp_pos _).trans_le hLoB
  have hc : 0 < c := (Real.exp_pos _).trans_le hLoC
  have hd : 0 < d := (Real.exp_pos _).trans_le hLoD
  have hCross : (Real.log a - Real.log b) -
      (Real.log c - Real.log d) = 4 * beta := by
    simpa [a, b, c, d,
      p4Q2FU_originalSU2WilsonPosteriorFourCornerEntry,
      p4Q2FS_originalSU2WilsonEveryLinkPosteriorCrossLog] using
      (p4Q2FS_originalSU2WilsonEveryLinkPosteriorCrossLog_eq_four_beta
        H beta hbeta right e)
  have hMinor := p4Q2FU_positiveFourCornerLog_crossing_eq_minor
    a b c d (4 * beta) ha hb hc hd hCross
  change a * d - b * c = (Real.exp (4 * beta) - 1) * (b * c)
  exact hMinor

/-- Explicit strictly positive beta-dependent lower bound for the 2x2
minor of the ORIGINAL interacting normalized Wilson posterior at EVERY
physical link, uniform in H,e,right. No condition on a source vector. -/
theorem p4Q2FU_originalSU2WilsonPosteriorMinor_explicit_uniform_lower
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    (Real.exp (4 * beta) - 1) * Real.exp (-32 * beta) ≤
      p4Q2FU_originalSU2WilsonPosteriorFourCornerMinor
        H beta hbeta right e := by
  let b := p4Q2FU_originalSU2WilsonPosteriorFourCornerEntry
    H beta hbeta right e false true
  let c := p4Q2FU_originalSU2WilsonPosteriorFourCornerEntry
    H beta hbeta right e true false
  have hB : Real.exp (-16 * beta) ≤ b :=
    (p4Q2FK_originalWilsonPosteriorConditionalDensity_twoSided
      H 2 (by norm_num) beta hbeta
      (originalWilsonExplicitIdentityBoundary H) right e
      (specialUnitaryTwoRotation Real.pi)).1
  have hC : Real.exp (-16 * beta) ≤ c :=
    (p4Q2FK_originalWilsonPosteriorConditionalDensity_twoSided
      H 2 (by norm_num) beta hbeta
      (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e 1).1
  have hBpos : 0 ≤ b :=
    (Real.exp_pos _).le.trans hB
  have hEpos : 0 ≤ Real.exp (-16 * beta) :=
    (Real.exp_pos _).le
  have hBC : Real.exp (-32 * beta) ≤ b * c := by
    have hE :
        Real.exp (-16 * beta) * Real.exp (-16 * beta) =
          Real.exp (-32 * beta) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← hE]
    calc
      Real.exp (-16 * beta) * Real.exp (-16 * beta) ≤
          b * Real.exp (-16 * beta) :=
        mul_le_mul_of_nonneg_right hB hEpos
      _ ≤ b * c := mul_le_mul_of_nonneg_left hC hBpos
  have hCoefNonneg : 0 ≤ Real.exp (4 * beta) - 1 := by
    have hExp : Real.exp 0 ≤ Real.exp (4 * beta) :=
      Real.exp_le_exp.mpr (by nlinarith [hbeta])
    rw [Real.exp_zero] at hExp
    linarith
  have hExact := p4Q2FU_originalSU2WilsonPosteriorMinor_eq_exact
    H beta hbeta right e
  rw [hExact]
  exact mul_le_mul_of_nonneg_left hBC hCoefNonneg

/-- For every positive beta, the actual posterior four-corner minor is
STRICTLY positive with a uniform explicit numerical lower certificate. -/
theorem p4Q2FU_originalSU2WilsonPosteriorMinor_pos
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 < p4Q2FU_originalSU2WilsonPosteriorFourCornerMinor
      H beta (le_of_lt hbeta) right e := by
  have hCoeff : 0 < Real.exp (4 * beta) - 1 := by
    have hExp : Real.exp 0 < Real.exp (4 * beta) :=
      Real.exp_lt_exp.mpr (by nlinarith [hbeta])
    rw [Real.exp_zero] at hExp
    linarith
  have hFloor :
      (Real.exp (4 * beta) - 1) * Real.exp (-32 * beta) ≤
        p4Q2FU_originalSU2WilsonPosteriorFourCornerMinor
          H beta (le_of_lt hbeta) right e :=
    p4Q2FU_originalSU2WilsonPosteriorMinor_explicit_uniform_lower
      H beta (le_of_lt hbeta) right e
  exact (mul_pos hCoeff (Real.exp_pos _)).trans_le hFloor

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FU_positiveFourCornerLog_crossing_eq_minor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FU_originalSU2WilsonPosteriorMinor_eq_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FU_originalSU2WilsonPosteriorMinor_explicit_uniform_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FU_originalSU2WilsonPosteriorMinor_pos
