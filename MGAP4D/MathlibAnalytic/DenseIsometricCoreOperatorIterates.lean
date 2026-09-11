import MGAP4D.MathlibAnalytic.DenseIsometricCoreOperatorCompletion
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

noncomputable section

open Function

namespace MGAP4D
namespace MathlibAnalytic

universe u v

namespace DenseIsometricCoreOperatorCompletion

variable
    {E : Type u} {H : Type v}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

/-- Iterating the completed operator on a represented core point is exactly the
represented iterate of the original bounded core operator. -/
theorem completedOperator_iterate_on_core
    (e : E →ₗ[ℝ] H)
    (hDense : DenseRange e)
    (hIsometry : ∀ x : E, ‖e x‖ = ‖x‖)
    (T : E →L[ℝ] E)
    (k : ℕ)
    (x : E) :
    (fun y : H => completedOperator e T y)^[k] (e x) =
      e ((fun z : E => T z)^[k] x) := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        completedOperator_on_core e hDense hIsometry T]

/-- Every iterate of the completed operator is bounded by the corresponding
power of the original core operator norm. -/
theorem completedOperator_iterate_norm_le
    (e : E →ₗ[ℝ] H)
    (hDense : DenseRange e)
    (hIsometry : ∀ x : E, ‖e x‖ = ‖x‖)
    (T : E →L[ℝ] E)
    (k : ℕ)
    (y : H) :
    ‖(fun z : H => completedOperator e T z)^[k] y‖ ≤
      ‖T‖ ^ k * ‖y‖ := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      calc
        ‖completedOperator e T
            ((fun z : H => completedOperator e T z)^[k] y)‖ ≤
            ‖T‖ *
              ‖(fun z : H => completedOperator e T z)^[k] y‖ :=
          completedOperator_norm_le e hDense hIsometry T _
        _ ≤ ‖T‖ * (‖T‖ ^ k * ‖y‖) :=
          mul_le_mul_of_nonneg_left ih (norm_nonneg T)
        _ = ‖T‖ ^ (Nat.succ k) * ‖y‖ := by
          rw [pow_succ]
          ring

end DenseIsometricCoreOperatorCompletion

end MathlibAnalytic
end MGAP4D

end