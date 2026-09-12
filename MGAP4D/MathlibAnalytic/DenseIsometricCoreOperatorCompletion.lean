import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Tactic

noncomputable section

open Function

namespace MGAP4D
namespace MathlibAnalytic

universe u v

/- Generic completion of a bounded operator from a norm-preserving dense linear
core into a complete ambient normed space.

This is the abstract functional-analytic layer used by the finite Wilson
excitation completion: no Yang--Mills structure occurs here. -/
namespace DenseIsometricCoreOperatorCompletion

variable
    {E : Type u} {H : Type v}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

/-- Apply the core operator and then the dense isometric representation. -/
def denseLinearMap
    (e : E →ₗ[ℝ] H) (T : E →L[ℝ] E) : E →ₗ[ℝ] H :=
  e.comp T.toLinearMap

@[simp] theorem denseLinearMap_apply
    (e : E →ₗ[ℝ] H) (T : E →L[ℝ] E) (x : E) :
    denseLinearMap e T x = e (T x) :=
  rfl

/-- The operator norm of the core operator bounds the represented dense map
when the dense representation preserves norms. -/
theorem denseLinearMap_norm_le
    (e : E →ₗ[ℝ] H)
    (hIsometry : ∀ x : E, ‖e x‖ = ‖x‖)
    (T : E →L[ℝ] E)
    (x : E) :
    ‖denseLinearMap e T x‖ ≤ ‖T‖ * ‖e x‖ := by
  rw [denseLinearMap_apply, hIsometry, hIsometry]
  exact T.le_opNorm x

/-- Unique bounded completion of `T` through the norm-preserving dense core
representation `e`. -/
noncomputable def completedOperator
    (e : E →ₗ[ℝ] H) (T : E →L[ℝ] E) : H →L[ℝ] H :=
  (denseLinearMap e T).extendOfNorm e

/-- The completion agrees with `T` on the represented dense core. -/
theorem completedOperator_on_core
    (e : E →ₗ[ℝ] H)
    (hDense : DenseRange e)
    (hIsometry : ∀ x : E, ‖e x‖ = ‖x‖)
    (T : E →L[ℝ] E)
    (x : E) :
    completedOperator e T (e x) = e (T x) := by
  change (denseLinearMap e T).extendOfNorm e (e x) = denseLinearMap e T x
  exact LinearMap.extendOfNorm_eq
    hDense ⟨‖T‖, denseLinearMap_norm_le e hIsometry T⟩ x

/-- The completed operator retains the core operator-norm bound everywhere. -/
theorem completedOperator_norm_le
    (e : E →ₗ[ℝ] H)
    (hDense : DenseRange e)
    (hIsometry : ∀ x : E, ‖e x‖ = ‖x‖)
    (T : E →L[ℝ] E)
    (y : H) :
    ‖completedOperator e T y‖ ≤ ‖T‖ * ‖y‖ := by
  have h := LinearMap.norm_extendOfNorm_apply_le
    (f := denseLinearMap e T)
    (e := e)
    hDense ‖T‖ (denseLinearMap_norm_le e hIsometry T) y
  simpa only [completedOperator] using h

/-- Completion cannot increase the operator norm. -/
theorem completedOperator_opNorm_le
    (e : E →ₗ[ℝ] H)
    (hDense : DenseRange e)
    (hIsometry : ∀ x : E, ‖e x‖ = ‖x‖)
    (T : E →L[ℝ] E) :
    ‖completedOperator e T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound
    (completedOperator e T) (norm_nonneg T)
  intro y
  exact completedOperator_norm_le e hDense hIsometry T y

/-- Density together with exact norm preservation gives the reverse operator
norm inequality. -/
theorem opNorm_le_completedOperator
    (e : E →ₗ[ℝ] H)
    (hDense : DenseRange e)
    (hIsometry : ∀ x : E, ‖e x‖ = ‖x‖)
    (T : E →L[ℝ] E) :
    ‖T‖ ≤ ‖completedOperator e T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound
    T (norm_nonneg (completedOperator e T))
  intro x
  have h := (completedOperator e T).le_opNorm (e x)
  rw [completedOperator_on_core e hDense hIsometry T x,
    hIsometry, hIsometry] at h
  exact h

/-- A bounded operator and its completion through a norm-preserving dense core
have exactly the same operator norm. -/
@[simp] theorem completedOperator_opNorm_eq
    (e : E →ₗ[ℝ] H)
    (hDense : DenseRange e)
    (hIsometry : ∀ x : E, ‖e x‖ = ‖x‖)
    (T : E →L[ℝ] E) :
    ‖completedOperator e T‖ = ‖T‖ :=
  le_antisymm
    (completedOperator_opNorm_le e hDense hIsometry T)
    (opNorm_le_completedOperator e hDense hIsometry T)

end DenseIsometricCoreOperatorCompletion

end MathlibAnalytic
end MGAP4D

end