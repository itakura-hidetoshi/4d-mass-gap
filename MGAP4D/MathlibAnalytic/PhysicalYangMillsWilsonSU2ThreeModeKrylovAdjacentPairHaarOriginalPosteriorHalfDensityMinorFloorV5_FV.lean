import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalEveryLinkPosteriorUniformMinorV5_FU
import Mathlib.Tactic

/-!
# P4-Q2-FV: genuine SU(2) Wilson conditional half-density minor floor

The physical uncentered Wilson receiver involves the inverse square
root of the ORIGINAL Wilson joint density.  P4-Q2-FU proves a
strict, volume-uniform 2x2 determinant floor for the TRUE normalized
Wilson one-link posterior density, at two physical left boundaries and
two distinct SU(2) right target-link values.

The quantitative algebraic passage from the density minor to its
POSITIVE square-root minor is

  0 <= delta <= a*d-b*c,  0<a,b,c,d<=M
  => delta <= 2*M*(sqrt(a*d)-sqrt(b*c)).

We instantiate delta = (exp(4 beta)-1)*exp(-32 beta)
and M = exp(16 beta), giving the exactly physical bound

  (exp(4 beta)-1)*exp(-32 beta)
    <= 2*exp(16 beta)*(sqrt(p00*p11)-sqrt(p01*p10)),

with the square-root minor STRICTLY POSITIVE at beta>0,
independent of physical link, right environment, finite spatial volume.

This is a two-point half-density obstruction, NOT a uniform integrated
L² frame bound: SU(2) Haar probability is atomless and a two-point
witness requires a further averaging/thickness argument.
No posterior replacement, Dobrushin, new axiom or continuum gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 650000

namespace GroundStatePosteriorJoint

/-- A strictly positive 2x2 density minor has a quantitative
square-root (Hellinger-amplitude) minor, with only one upper-entry
factor M. This scalar lemma does not assume any probability law. -/
theorem p4Q2FV_positiveDensityMinor_controls_sqrtMinor
    (a b c d M delta : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (haM : a ≤ M) (hbM : b ≤ M)
    (hcM : c ≤ M) (hdM : d ≤ M)
    (hdelta : 0 ≤ delta)
    (hminor : delta ≤ a * d - b * c) :
    delta ≤ 2 * M *
      (Real.sqrt (a * d) - Real.sqrt (b * c)) := by
  have hM : 0 ≤ M := (ha.le).trans haM
  have had : 0 ≤ a * d := (mul_pos ha hd).le
  have hbc : 0 ≤ b * c := (mul_pos hb hc).le
  have hupperAd : a * d ≤ M * M := by
    calc
      a * d ≤ M * d :=
        mul_le_mul_of_nonneg_right haM hd.le
      _ ≤ M * M :=
        mul_le_mul_of_nonneg_left hdM hM
  have hupperBc : b * c ≤ M * M := by
    calc
      b * c ≤ M * c :=
        mul_le_mul_of_nonneg_right hbM hc.le
      _ ≤ M * M :=
        mul_le_mul_of_nonneg_left hcM hM
  have hSqrtAd :
      Real.sqrt (a * d) ≤ M := by
    have hnonneg : 0 ≤ Real.sqrt (a * d) := Real.sqrt_nonneg _
    nlinarith [Real.sq_sqrt had]
  have hSqrtBc :
      Real.sqrt (b * c) ≤ M := by
    have hnonneg : 0 ≤ Real.sqrt (b * c) := Real.sqrt_nonneg _
    nlinarith [Real.sq_sqrt hbc]
  let x := Real.sqrt (a * d)
  let y := Real.sqrt (b * c)
  have hx : 0 < x := Real.sqrt_pos.mpr (mul_pos ha hd)
  have hy : 0 < y := Real.sqrt_pos.mpr (mul_pos hb hc)
  have hdet : a * d - b * c = (x - y) * (x + y) := by
    dsimp [x, y]
    nlinarith [Real.sq_sqrt had, Real.sq_sqrt hbc]
  have hxy : 0 ≤ x - y := by
    have hnonneg : 0 ≤ a * d - b * c := hdelta.trans hminor
    rw [hdet] at hnonneg
    nlinarith
  have hsum : x + y ≤ 2 * M := by
    dsimp [x, y]
    linarith
  calc
    delta ≤ a * d - b * c := hminor
    _ = (x - y) * (x + y) := hdet
    _ ≤ 2 * M * (x - y) := by
      have h := mul_le_mul_of_nonneg_left hsum hxy
      nlinarith

/-- The EXACT true Wilson conditional four-corner half-density
determinant (not a Haar-posterior surrogate). -/
noncomputable def p4Q2FV_originalSU2WilsonPosteriorHalfDensityMinor
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  Real.sqrt
      (p4Q2FU_originalSU2WilsonPosteriorFourCornerEntry
          H beta hbeta right e false false *
        p4Q2FU_originalSU2WilsonPosteriorFourCornerEntry
          H beta hbeta right e true true) -
    Real.sqrt
      (p4Q2FU_originalSU2WilsonPosteriorFourCornerEntry
          H beta hbeta right e false true *
        p4Q2FU_originalSU2WilsonPosteriorFourCornerEntry
          H beta hbeta right e true false)

/-- Explicit quantitative half-density minor bound of the ACTUAL
interacting SU(2) Wilson one-link posterior. The coefficient is
independent of spatial volume H, link e and right environment. -/
theorem p4Q2FV_originalSU2WilsonPosteriorHalfDensityMinor_uniform_floor
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    (Real.exp (4 * beta) - 1) * Real.exp (-32 * beta) ≤
      2 * Real.exp (16 * beta) *
        p4Q2FV_originalSU2WilsonPosteriorHalfDensityMinor
          H beta hbeta right e := by
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
  have hBound (row col : Bool) :
      Real.exp (-16 * beta) ≤
        p4Q2FU_originalSU2WilsonPosteriorFourCornerEntry
          H beta hbeta right e row col ∧
        p4Q2FU_originalSU2WilsonPosteriorFourCornerEntry
          H beta hbeta right e row col ≤ M := by
    unfold p4Q2FU_originalSU2WilsonPosteriorFourCornerEntry
    exact
      p4Q2FK_originalWilsonPosteriorConditionalDensity_twoSided
        H 2 (by norm_num) beta hbeta
        (if row then p4Q2FQ_originalSU2LeftPiRotationAtLink H e
          else originalWilsonExplicitIdentityBoundary H)
        right e
        (if col then specialUnitaryTwoRotation Real.pi
          else (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))
  have ha : 0 < a := (Real.exp_pos _).trans_le (hBound false false).1
  have hb : 0 < b := (Real.exp_pos _).trans_le (hBound false true).1
  have hc : 0 < c := (Real.exp_pos _).trans_le (hBound true false).1
  have hd : 0 < d := (Real.exp_pos _).trans_le (hBound true true).1
  have haM : a ≤ M := (hBound false false).2
  have hbM : b ≤ M := (hBound false true).2
  have hcM : c ≤ M := (hBound true false).2
  have hdM : d ≤ M := (hBound true true).2
  have hdelta : 0 ≤ delta := by
    dsimp [delta]
    have hExp : (1 : ℝ) ≤ Real.exp (4 * beta) := by
      calc
        (1 : ℝ) = Real.exp 0 := by simp
        _ ≤ Real.exp (4 * beta) :=
          Real.exp_le_exp.mpr (by nlinarith [hbeta])
    exact mul_nonneg (sub_nonneg.mpr hExp) (Real.exp_pos _).le
  have hminor : delta ≤ a * d - b * c := by
    simpa only [delta, a, b, c, d,
      p4Q2FU_originalSU2WilsonPosteriorFourCornerMinor] using
      (p4Q2FU_originalSU2WilsonPosteriorMinor_explicit_uniform_lower
        H beta hbeta right e)
  have hMain :=
    p4Q2FV_positiveDensityMinor_controls_sqrtMinor
      a b c d M delta ha hb hc hd haM hbM hcM hdM hdelta hminor
  simpa only [delta, M, a, b, c, d,
    p4Q2FV_originalSU2WilsonPosteriorHalfDensityMinor] using hMain

/-- Strict positivity of the true posterior half-density crossing
at EVERY physical SU(2) right spatial link for positive beta.
This is still only a pointwise two-corner statement. -/
theorem p4Q2FV_originalSU2WilsonPosteriorHalfDensityMinor_pos
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 < p4Q2FV_originalSU2WilsonPosteriorHalfDensityMinor
      H beta (le_of_lt hbeta) right e := by
  have hFloor :=
    p4Q2FV_originalSU2WilsonPosteriorHalfDensityMinor_uniform_floor
      H beta (le_of_lt hbeta) right e
  have hdelta : 0 < (Real.exp (4 * beta) - 1) *
      Real.exp (-32 * beta) := by
    have hExp : 1 < Real.exp (4 * beta) := by
      calc
        (1 : ℝ) = Real.exp 0 := by simp
        _ < Real.exp (4 * beta) :=
          Real.exp_lt_exp.mpr (by nlinarith [hbeta])
    exact mul_pos (sub_pos.mpr hExp) (Real.exp_pos _)
  have hM : 0 < 2 * Real.exp (16 * beta) :=
    mul_pos (by norm_num) (Real.exp_pos _)
  by_contra hnot
  have hnonpos :
      p4Q2FV_originalSU2WilsonPosteriorHalfDensityMinor
        H beta (le_of_lt hbeta) right e ≤ 0 := le_of_not_gt hnot
  have hprod :
      2 * Real.exp (16 * beta) *
        p4Q2FV_originalSU2WilsonPosteriorHalfDensityMinor
          H beta (le_of_lt hbeta) right e ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hM.le hnonpos
  exact (not_le_of_gt hdelta) (le_trans hFloor hprod)

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FV_positiveDensityMinor_controls_sqrtMinor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FV_originalSU2WilsonPosteriorHalfDensityMinor_uniform_floor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FV_originalSU2WilsonPosteriorHalfDensityMinor_pos
