import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalEveryLinkPosteriorUniformMinorV5_FU
import Mathlib.Tactic

/-!
# P4-Q2-FY: quantitative all-link SU(2) original Wilson posterior response witness

FU establishes an explicitly positive, volume-INDEPENDENT determinant
floor for the TRUE normalized Wilson one-link conditional density on the
two physical left boundaries A0 and Ae(pi), and inserted target values
g=1 and R(pi):

 delta_beta = (exp(4 beta)-1)*exp(-32 beta) <= a*d-b*c.

FK bounds EACH density entry from above by M_beta=exp(16 beta).
An elementary four-corner stability estimate then proves

  delta_beta <= M_beta*(|a-c|+|b-d|),

so at least one actual inserted SU(2) target has

  |p_beta(g | A0, right_off_e) - p_beta(g | Ae(pi), right_off_e)|
    >= delta_beta/(2*M_beta)

with a strictly POSITIVE, volume/link/background-independent coefficient
for every beta>0.

This is stronger than FS's qualitative pointwise sensitivity, but does
NOT mistake two Haar-null test points for an integrated Haar L² lower
bound. FX gives positive (not uniform) true posterior Haar L² separation.
The remaining task is a quantitatively uniform Haar-integration argument
and then the SAME-source actual FG RMS link-mass frame bound.

No surrogate density, Dobrushin, additional axiom, sorry or
Yang--Mills continuum mass gap is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 650000

namespace GroundStatePosteriorJoint

/-- A bounded two-row density minor controls the sum of the two
pointwise row differences. Completely scalar and assumption-explicit. -/
theorem p4Q2FY_minor_le_upper_times_twoRowDifferences
    (a b c d M delta : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hcM : c ≤ M) (hdM : d ≤ M)
    (hMinor : delta ≤ a * d - b * c) :
    delta ≤ M * (|a - c| + |b - d|) := by
  have hFirst : (a - c) * d ≤ |a - c| * d :=
    mul_le_mul_of_nonneg_right (le_abs_self (a - c)) hd
  have hSecond : c * (d - b) ≤ c * |d - b| :=
    mul_le_mul_of_nonneg_left (le_abs_self (d - b)) hc
  have hThird : |a - c| * d ≤ |a - c| * M :=
    mul_le_mul_of_nonneg_left hdM (abs_nonneg _)
  have hFourth : c * |d - b| ≤ M * |d - b| :=
    mul_le_mul_of_nonneg_right hcM (abs_nonneg _)
  calc
    delta ≤ a * d - b * c := hMinor
    _ = (a - c) * d + c * (d - b) := by ring
    _ ≤ |a - c| * d + c * |d - b| := add_le_add hFirst hSecond
    _ ≤ |a - c| * M + M * |d - b| := add_le_add hThird hFourth
    _ = M * (|a - c| + |b - d|) := by
      rw [abs_sub_comm d b]
      ring

/-- At least one of the two physical inserted values has a definite
row separation, not merely an existence statement with no modulus. -/
theorem p4Q2FY_minor_controls_max_twoRowDifferences
    (a b c d M delta : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hcM : c ≤ M) (hdM : d ≤ M)
    (hM : 0 < M)
    (hMinor : delta ≤ a * d - b * c) :
    delta / (2 * M) ≤ max (|a - c|) (|b - d|) := by
  have hMinorBound :=
    p4Q2FY_minor_le_upper_times_twoRowDifferences
      a b c d M delta hc hd hcM hdM hMinor
  have ha := le_max_left (|a - c|) (|b - d|)
  have hb := le_max_right (|a - c|) (|b - d|)
  have hSum :
      |a - c| + |b - d| ≤ 2 * max (|a - c|) (|b - d|) := by
    linarith
  have hMul := mul_le_mul_of_nonneg_left hSum hM.le
  have hDen : 0 < 2 * M := mul_pos (by norm_num) hM
  apply (div_le_iff₀ hDen).2
  calc
    delta ≤ M * (|a - c| + |b - d|) := hMinorBound
    _ ≤ M * (2 * max (|a - c|) (|b - d|)) := hMul
    _ = max (|a - c|) (|b - d|) * (2 * M) := by ring

/-- Sharp explicit model-independent beta coefficient extracted from
the true SU(2) posterior determinant and density upper envelope. -/
noncomputable def p4Q2FY_originalWilsonPosteriorPointwiseSeparationFloor
    (beta : ℝ) : ℝ :=
  ((Real.exp (4 * beta) - 1) * Real.exp (-32 * beta)) /
    (2 * Real.exp (16 * beta))

theorem p4Q2FY_originalWilsonPosteriorPointwiseSeparationFloor_pos
    (beta : ℝ) (hbeta : 0 < beta) :
    0 < p4Q2FY_originalWilsonPosteriorPointwiseSeparationFloor beta := by
  unfold p4Q2FY_originalWilsonPosteriorPointwiseSeparationFloor
  have he : 1 < Real.exp (4 * beta) := by
    calc
      (1 : ℝ) = Real.exp 0 := by norm_num
      _ < Real.exp (4 * beta) := Real.exp_lt_exp.mpr (by linarith)
  exact div_pos
    (mul_pos (sub_pos.mpr he) (Real.exp_pos _))
    (mul_pos (by norm_num) (Real.exp_pos _))

/-- At EVERY original physical spatial SU(2) link and ANY finite-volume
right environment, the REAL normalized Wilson posterior has an explicit,
uniform lower bound on its row separation at the two original target
values. No Haar point masses are invented. -/
theorem p4Q2FY_originalSU2WilsonPosteriorTwoPointRowDifference_quantitative
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    p4Q2FY_originalWilsonPosteriorPointwiseSeparationFloor beta ≤
      max
        (|p4Q2FU_originalSU2WilsonPosteriorFourCornerEntry
            H beta hbeta right e false false -
          p4Q2FU_originalSU2WilsonPosteriorFourCornerEntry
            H beta hbeta right e true false|)
        (|p4Q2FU_originalSU2WilsonPosteriorFourCornerEntry
            H beta hbeta right e false true -
          p4Q2FU_originalSU2WilsonPosteriorFourCornerEntry
            H beta hbeta right e true true|) := by
  let a := p4Q2FU_originalSU2WilsonPosteriorFourCornerEntry
    H beta hbeta right e false false
  let b := p4Q2FU_originalSU2WilsonPosteriorFourCornerEntry
    H beta hbeta right e false true
  let c := p4Q2FU_originalSU2WilsonPosteriorFourCornerEntry
    H beta hbeta right e true false
  let d := p4Q2FU_originalSU2WilsonPosteriorFourCornerEntry
    H beta hbeta right e true true
  let M := Real.exp (16 * beta)
  let delta := (Real.exp (4 * beta) - 1) * Real.exp (-32 * beta)
  have hcBounds :=
    p4Q2FK_originalWilsonPosteriorConditionalDensity_twoSided
      H 2 (by norm_num) beta hbeta
      (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e
      (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)
  have hdBounds :=
    p4Q2FK_originalWilsonPosteriorConditionalDensity_twoSided
      H 2 (by norm_num) beta hbeta
      (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e
      (specialUnitaryTwoRotation Real.pi)
  have hc : 0 ≤ c := (Real.exp_pos _).le.trans hcBounds.1
  have hd : 0 ≤ d := (Real.exp_pos _).le.trans hdBounds.1
  have hcM : c ≤ M := hcBounds.2
  have hdM : d ≤ M := hdBounds.2
  have hM : 0 < M := Real.exp_pos _
  have hMinor : delta ≤ a * d - b * c := by
    simpa only [delta, a, b, c, d,
      p4Q2FU_originalSU2WilsonPosteriorFourCornerMinor] using
      (p4Q2FU_originalSU2WilsonPosteriorMinor_explicit_uniform_lower
        H beta hbeta right e)
  have hQuant :=
    p4Q2FY_minor_controls_max_twoRowDifferences
      a b c d M delta hc hd hcM hdM hM hMinor
  simpa only [a, b, c, d, M, delta,
    p4Q2FY_originalWilsonPosteriorPointwiseSeparationFloor] using hQuant

/-- Explicit TRUE-posterior quantitative response witness at one of the
two physical SU(2) candidate link values, uniform over H,e,right. -/
theorem p4Q2FY_originalSU2WilsonPosterior_exists_inserted_value_quantitative
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    ∃ g : Matrix.specialUnitaryGroup (Fin 2) ℂ,
      p4Q2FY_originalWilsonPosteriorPointwiseSeparationFloor beta ≤
        |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
            H 2 (by norm_num) beta (le_of_lt hbeta)
            (originalWilsonExplicitIdentityBoundary H) right e g -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
            H 2 (by norm_num) beta (le_of_lt hbeta)
            (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e g| := by
  have hBound :=
    p4Q2FY_originalSU2WilsonPosteriorTwoPointRowDifference_quantitative
      H beta (le_of_lt hbeta) right e
  rcases (le_max_iff.mp hBound) with hOne | hPi
  · exact ⟨1, hOne⟩
  · exact ⟨specialUnitaryTwoRotation Real.pi, hPi⟩

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FY_minor_le_upper_times_twoRowDifferences
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FY_minor_controls_max_twoRowDifferences
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FY_originalWilsonPosteriorPointwiseSeparationFloor_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FY_originalSU2WilsonPosteriorTwoPointRowDifference_quantitative
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FY_originalSU2WilsonPosterior_exists_inserted_value_quantitative
