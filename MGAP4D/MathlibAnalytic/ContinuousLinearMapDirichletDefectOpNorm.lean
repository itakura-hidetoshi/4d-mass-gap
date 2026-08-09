import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

noncomputable section

namespace MGAP4D
namespace MathlibAnalytic

universe u

/-- A pointwise quadratic Dirichlet coercivity estimate for a bounded operator
controls its operator norm with the corresponding sharp square-root factor.

This is the generic functional-analytic converse needed to turn a literal
Poincare inequality into a transfer-operator contraction. -/
theorem continuousLinearMap_norm_le_sqrt_one_sub_of_dirichlet_coercive
    {E : Type u}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →L[ℝ] E)
    (c : ℝ)
    (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1)
    (hcoercive : ∀ x : E,
      c * ‖x‖ ^ 2 ≤ ‖x‖ ^ 2 - ‖T x‖ ^ 2)
    (x : E) :
    ‖T x‖ ≤ Real.sqrt (1 - c) * ‖x‖ := by
  have hsub : 0 ≤ 1 - c := sub_nonneg.mpr hc1
  have hsqrt : 0 ≤ Real.sqrt (1 - c) := Real.sqrt_nonneg _
  have hsq :
      ‖T x‖ ^ 2 ≤ (Real.sqrt (1 - c) * ‖x‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hsub]
    nlinarith [hcoercive x]
  nlinarith [norm_nonneg (T x), norm_nonneg x]

/-- Operator-norm form of the generic Dirichlet coercivity converse. -/
theorem continuousLinearMap_opNorm_le_sqrt_one_sub_of_dirichlet_coercive
    {E : Type u}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →L[ℝ] E)
    (c : ℝ)
    (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1)
    (hcoercive : ∀ x : E,
      c * ‖x‖ ^ 2 ≤ ‖x‖ ^ 2 - ‖T x‖ ^ 2) :
    ‖T‖ ≤ Real.sqrt (1 - c) := by
  apply ContinuousLinearMap.opNorm_le_bound T (Real.sqrt_nonneg _)
  intro x
  exact continuousLinearMap_norm_le_sqrt_one_sub_of_dirichlet_coercive
    T c hc0 hc1 hcoercive x

/-- Squared operator-norm form:

`||T||^2 <= 1 - c`.

This is the exact statement needed to lower-bound the intrinsic transfer defect
`1 - ||T||^2` by a Poincare coefficient `c`. -/
theorem continuousLinearMap_opNorm_sq_le_one_sub_of_dirichlet_coercive
    {E : Type u}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →L[ℝ] E)
    (c : ℝ)
    (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1)
    (hcoercive : ∀ x : E,
      c * ‖x‖ ^ 2 ≤ ‖x‖ ^ 2 - ‖T x‖ ^ 2) :
    ‖T‖ ^ 2 ≤ 1 - c := by
  have hop :=
    continuousLinearMap_opNorm_le_sqrt_one_sub_of_dirichlet_coercive
      T c hc0 hc1 hcoercive
  have hsub : 0 ≤ 1 - c := sub_nonneg.mpr hc1
  have hsqrt_sq : (Real.sqrt (1 - c)) ^ 2 = 1 - c :=
    Real.sq_sqrt hsub
  nlinarith [norm_nonneg T, Real.sqrt_nonneg (1 - c)]

/-- Equivalently, every valid Poincare coefficient is bounded above by the
operator's intrinsic squared norm defect. -/
theorem continuousLinearMap_le_one_sub_opNorm_sq_of_dirichlet_coercive
    {E : Type u}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →L[ℝ] E)
    (c : ℝ)
    (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1)
    (hcoercive : ∀ x : E,
      c * ‖x‖ ^ 2 ≤ ‖x‖ ^ 2 - ‖T x‖ ^ 2) :
    c ≤ 1 - ‖T‖ ^ 2 := by
  have h :=
    continuousLinearMap_opNorm_sq_le_one_sub_of_dirichlet_coercive
      T c hc0 hc1 hcoercive
  linarith

end MathlibAnalytic
end MGAP4D

end