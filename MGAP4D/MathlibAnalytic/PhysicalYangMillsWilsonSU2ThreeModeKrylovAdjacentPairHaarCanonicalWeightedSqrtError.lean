import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarCanonicalRightLinkSqrtError
import Mathlib.Tactic

/-!
# P4-Q1: exact canonical Wilson weighted squared inverse-sqrt error

The original genuine positive-beta joint law has density W_beta
with respect to original pair Haar. The canonical continuous
representative W_(beta,c) from #5296 equals W_beta pair-Haar-a.e.
This file establishes the POINTWISE identity and explicit Harnack
bound for the precise weighted integrand in the original joint L²
candidate error, using the actual Wilson weights and no new law:

  a * (1/sqrt(a) - 1/sqrt(b))²
    = (1 - sqrt(a/b))²
    <= (R-1)²

where a is the original canonical weight at the true right boundary,
b is the same canonical weight with ONE right link fixed to identity,
and R = exp(16 beta). Positivity is proved for every configuration.

The identities are pointwise on the CANONICAL continuous versions.
They must be transported only a.e. to the original L² quotient
representatives before any joint-law integration. The full spatial
link sum still needs a separate quantitative estimate. No Dobrushin,
replacement law, asserted volume-uniform sum, or continuum gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

/-- Pure real algebra: the original-density weighted inverse-sqrt
error is EXACTLY the normalized sqrt-density-ratio error. -/
theorem real_weighted_invSqrt_sub_sq_eq_sqrtRatio_sq
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a * ((1 : ℝ) / Real.sqrt a - (1 : ℝ) / Real.sqrt b) ^ 2 =
      (1 - Real.sqrt (a / b)) ^ 2 := by
  let x : ℝ := Real.sqrt a
  let y : ℝ := Real.sqrt b
  have hxpos : 0 < x := Real.sqrt_pos.2 ha
  have hypos : 0 < y := Real.sqrt_pos.2 hb
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have hyne : y ≠ 0 := ne_of_gt hypos
  have hxsq : x ^ 2 = a := Real.sq_sqrt ha.le
  rw [Real.sqrt_div ha.le]
  change a * ((1 : ℝ) / x - (1 : ℝ) / y) ^ 2 =
    (1 - x / y) ^ 2
  rw [← hxsq]
  field_simp [hxne, hyne]

/-- Symmetric positive Harnack comparison gives a weighted
inverse-square-root error bounded by the SAME coefficient (R-1)². -/
theorem real_weighted_invSqrt_sub_sq_le_harnack
    (a b R : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hR : 1 ≤ R) (hab : a ≤ R * b) (hba : b ≤ R * a) :
    a * ((1 : ℝ) / Real.sqrt a - (1 : ℝ) / Real.sqrt b) ^ 2 ≤
      (R - 1) ^ 2 := by
  calc
    a * ((1 : ℝ) / Real.sqrt a - (1 : ℝ) / Real.sqrt b) ^ 2 =
      (1 - Real.sqrt (a / b)) ^ 2 :=
      real_weighted_invSqrt_sub_sq_eq_sqrtRatio_sq a b ha hb
    _ ≤ (R - 1) ^ 2 :=
      real_one_sub_sqrt_ratio_sq_le_harnack a b R ha hb hR hab hba

local instance p4Q1WeightedTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q1WeightedCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q1WeightedSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q1WeightedMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q1WeightedBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q1WeightedSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- At every concrete SU(2) left-right boundary and right spatial
link e, the ORIGINAL canonical continuous Wilson joint density
weights the inverse-sqrt candidate error by at most
(exp(16 beta)-1)², independently of finite spatial extent H. -/
theorem originalWilsonContinuousPhysicalJointWeight_weighted_invSqrt_frozen_sq_le
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    originalWilsonContinuousPhysicalJointWeight H beta hbeta (A, B) *
      ((1 : ℝ) /
          Real.sqrt (originalWilsonContinuousPhysicalJointWeight H beta hbeta (A, B)) -
        (1 : ℝ) /
          Real.sqrt (originalWilsonContinuousPhysicalJointWeight H beta hbeta
            (A, Function.update B e (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)))) ^ 2 ≤
      (Real.exp (16 * beta) - 1) ^ 2 := by
  let a := originalWilsonContinuousPhysicalJointWeight H beta hbeta (A, B)
  let b := originalWilsonContinuousPhysicalJointWeight H beta hbeta
    (A, Function.update B e (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))
  have ha : 0 < a :=
    originalWilsonContinuousPhysicalJointWeight_pos H beta hbeta (A, B)
  have hb : 0 < b :=
    originalWilsonContinuousPhysicalJointWeight_pos H beta hbeta
      (A, Function.update B e (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))
  calc
    a * ((1 : ℝ) / Real.sqrt a - (1 : ℝ) / Real.sqrt b) ^ 2 =
        (1 - Real.sqrt (a / b)) ^ 2 :=
      real_weighted_invSqrt_sub_sq_eq_sqrtRatio_sq a b ha hb
    _ ≤ (Real.exp (16 * beta) - 1) ^ 2 :=
      originalWilsonContinuousPhysicalJointWeight_rightLink_sqrtRatio_sq_le
        H beta hbeta A B e

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
