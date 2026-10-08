import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarCanonicalRightLinkHarnack
import Mathlib.Tactic

/-!
# P4-Q1: normalized original Wilson one-right-link sqrt-ratio error

PR #5304 established an exact one-link comparison of the canonical
continuous representative of the ORIGINAL physical SU(2) Wilson
ground-state joint density, with volume-independent factor exp(16 beta).
The resulting ratio is a purely LOCAL density ratio, not a new
posterior or an arbitrary pointwise version of an L2 quotient.

For any two strictly positive real weights a,b with symmetric
Harnack factor R>=1, the following elementary but quantitative
estimate holds:

  (1 - sqrt(a/b))^2 <= (R-1)^2.

The proof uses the reciprocal Harnack inequality; neither side
alone is sufficient for this bound with the same constant.

We apply it to a=W_c(A,B) and b=W_c(A,B[e<-1]),
R=exp(16 beta), for every spatial volume H, beta>=0 and all
configurations. This is exactly the normalized squared pointwise
error appearing when the transported original joint vacuum
1/sqrt(W_c) is approximated by the unregularized retained-right-link
candidate 1/sqrt(W_c(A,B[e<-1])) under the genuine joint law.

This file proves the POINTWISE estimate. Integration against the
actual joint measure and the L2 witness construction are subsequent
independent steps. No volume-uniform bound for a SUM over all links,
Dobrushin coefficient, or continuum mass gap is claimed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

/-- Positive two-sided weight Harnack bounds imply a relative
square-root deviation bound, with constant R-1 tending to zero as
R tends to one. -/
theorem real_one_sub_sqrt_ratio_sq_le_harnack
    (a b R : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hR : 1 ≤ R) (hab : a ≤ R * b) (hba : b ≤ R * a) :
    (1 - Real.sqrt (a / b)) ^ 2 ≤ (R - 1) ^ 2 := by
  let r : ℝ := a / b
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hrpos : 0 < r := div_pos ha hb
  have hrup : r ≤ R := by
    exact (div_le_iff₀ hb).2 hab
  have hrr : 1 ≤ R * r := by
    have hr' : (1 : ℝ) ≤ (R * a) / b := by
      apply (le_div_iff₀ hb).2
      simpa only [one_mul] using hba
    simpa only [r, mul_div_assoc] using hr'
  have hquad : R * (2 - R) ≤ 1 := by
    nlinarith [sq_nonneg (R - 1)]
  have hrlow : 2 - R ≤ r := by
    by_contra hn
    have hlt : r < 2 - R := lt_of_not_ge hn
    have hm : R * r < R * (2 - R) := mul_lt_mul_of_pos_left hlt hRpos
    linarith
  have hratio_abs : |r - 1| ≤ R - 1 := by
    apply abs_le.mpr
    constructor <;> linarith
  have hsnonneg : 0 ≤ Real.sqrt r := Real.sqrt_nonneg r
  have hsq : (Real.sqrt r) ^ 2 = r := Real.sq_sqrt hrpos.le
  have hrootfactor : (Real.sqrt r - 1) * (Real.sqrt r + 1) = r - 1 := by
    nlinarith
  have hfactor_bound : (1 : ℝ) ≤ |Real.sqrt r + 1| := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hroot_abs : |Real.sqrt r - 1| ≤ |r - 1| := by
    calc
      |Real.sqrt r - 1| = |Real.sqrt r - 1| * 1 := by ring
      _ ≤ |Real.sqrt r - 1| * |Real.sqrt r + 1| :=
        mul_le_mul_of_nonneg_left hfactor_bound (abs_nonneg _)
      _ = |r - 1| := by rw [← abs_mul, hrootfactor]
  have hroot_bound : |Real.sqrt r - 1| ≤ R - 1 :=
    le_trans hroot_abs hratio_abs
  have hfact : 0 ≤
      (R - 1 - |Real.sqrt r - 1|) * (R - 1 + |Real.sqrt r - 1|) :=
    mul_nonneg (sub_nonneg.mpr hroot_bound) (by positivity)
  change (1 - Real.sqrt r) ^ 2 ≤ (R - 1) ^ 2
  nlinarith [hfact, sq_abs (Real.sqrt r - 1)]

local instance p4Q1RatioTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q1RatioCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q1RatioSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q1RatioMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q1RatioBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q1RatioSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Direct original SU(2) Wilson normalized sqrt-ratio error:
ONE target right-link identity-frozen weight approximates the
original joint weight with squared relative error at most
(exp(16 beta)-1)^2, independently of finite spatial extent H. -/
theorem originalWilsonContinuousPhysicalJointWeight_rightLink_sqrtRatio_sq_le
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    (1 - Real.sqrt (
      originalWilsonContinuousPhysicalJointWeight H beta hbeta (A, B) /
      originalWilsonContinuousPhysicalJointWeight H beta hbeta
        (A, Function.update B e (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)))) ^ 2 ≤
      (Real.exp (16 * beta) - 1) ^ 2 := by
  let a := originalWilsonContinuousPhysicalJointWeight H beta hbeta (A, B)
  let b := originalWilsonContinuousPhysicalJointWeight H beta hbeta
    (A, Function.update B e (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))
  let R : ℝ := Real.exp (16 * beta)
  have ha : 0 < a :=
    originalWilsonContinuousPhysicalJointWeight_pos H beta hbeta (A, B)
  have hb : 0 < b :=
    originalWilsonContinuousPhysicalJointWeight_pos H beta hbeta
      (A, Function.update B e (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))
  have hR : 1 ≤ R := by
    have hx : 0 ≤ (16 : ℝ) * beta := mul_nonneg (by norm_num) hbeta
    have h := Real.add_one_le_exp (16 * beta)
    dsimp [R]
    linarith
  have hab : a ≤ R * b :=
    originalWilsonContinuousPhysicalJointWeight_le_exp_sixteen_mul_frozen
      H beta hbeta A B e
  have hba : b ≤ R * a :=
    originalWilsonContinuousPhysicalJointWeight_frozen_le_exp_sixteen_mul
      H beta hbeta A B e
  exact real_one_sub_sqrt_ratio_sq_le_harnack a b R ha hb hR hab hba

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
