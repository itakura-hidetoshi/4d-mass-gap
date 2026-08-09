import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProductSpace

namespace ContinuousLinearMap.IsPositive

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {T : E →L[ℝ] E}

/-- For a positive bounded operator on a real Hilbert space, the operator norm
is the supremum of the Rayleigh quotient without an absolute value.

Mathlib already proves the absolute-value formula for every symmetric operator;
positivity removes the absolute value pointwise. -/
theorem norm_eq_iSup_rayleighQuotient_real
    (hT : T.IsPositive) :
    ‖T‖ = ⨆ x : E, T.rayleighQuotient x := by
  rw [T.norm_eq_iSup_rayleighQuotient hT.isSymmetric]
  apply congrArg (fun f : E → ℝ => ⨆ x, f x)
  funext x
  rw [abs_of_nonneg]
  exact div_nonneg (hT.re_inner_nonneg_left x) (sq_nonneg ‖x‖)

/-- Every strict lower bound on the norm of a positive bounded operator is
beaten by an actual Rayleigh quotient.  No finite-dimensionality, compactness,
or norm attainment is required. -/
theorem exists_rayleighQuotient_gt_of_lt_norm
    (hT : T.IsPositive) {r : ℝ} (hr : r < ‖T‖) :
    ∃ x : E, r < T.rayleighQuotient x := by
  by_contra h
  push Not at h
  have hle : ‖T‖ ≤ r := by
    rw [norm_eq_iSup_rayleighQuotient_real (T := T) hT]
    exact ciSup_le h
  exact (not_le_of_gt hr) hle

/-- A positive bounded operator admits unit vectors whose quadratic form beats
any nonnegative strict lower bound on its operator norm. -/
theorem exists_unit_inner_gt_of_lt_norm
    (hT : T.IsPositive) {r : ℝ}
    (hr_nonneg : 0 ≤ r) (hr : r < ‖T‖) :
    ∃ x : E, ‖x‖ = 1 ∧ r < inner ℝ (T x) x := by
  rcases exists_rayleighQuotient_gt_of_lt_norm (T := T) hT hr with ⟨x, hxray⟩
  have hx : x ≠ 0 := by
    intro hx0
    subst x
    simp only [ContinuousLinearMap.rayleighQuotient_apply_zero] at hxray
    linarith
  have hxnorm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let y : E := ‖x‖⁻¹ • x
  have hy_norm : ‖y‖ = 1 := by
    dsimp [y]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxnorm_pos)]
    simp [hxnorm_pos.ne']
  have hinv : (‖x‖⁻¹ : ℝ) ≠ 0 := inv_ne_zero hxnorm_pos.ne'
  have hy_ray : T.rayleighQuotient y = T.rayleighQuotient x := by
    dsimp [y]
    exact T.rayleigh_smul x hinv
  have hy_inner : T.rayleighQuotient y = inner ℝ (T y) y := by
    simp [ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply, hy_norm]
  refine ⟨y, hy_norm, ?_⟩
  rw [← hy_inner, hy_ray]
  exact hxray

/-- Exact logarithmic-rate bridge for a positive bounded operator.

For every positive lattice spacing `a`, positive operator norm, and positive
error tolerance `eps`, there is a unit state whose one-step quadratic energy
obeys

`(1 - ⟪T x, x⟫) / a < -log ‖T‖ / a + eps`.

The proof chooses the Rayleigh threshold
`r = ‖T‖ * exp (-a * eps)` and uses `log z ≤ z - 1`.
Consequently no factor two is lost when passing from an intrinsic transfer
operator norm to a generator-scale upper bound. -/
theorem exists_unit_discreteEnergy_lt_logRate_add
    (hT : T.IsPositive) {a eps : ℝ}
    (ha : 0 < a) (hTnorm : 0 < ‖T‖) (heps : 0 < eps) :
    ∃ x : E, ‖x‖ = 1 ∧
      (1 - inner ℝ (T x) x) / a <
        -Real.log ‖T‖ / a + eps := by
  let theta : ℝ := Real.exp (-a * eps)
  have htheta_pos : 0 < theta := by
    dsimp [theta]
    exact Real.exp_pos _
  have htheta_lt : theta < 1 := by
    dsimp [theta]
    rw [Real.exp_lt_one_iff]
    nlinarith
  let r : ℝ := ‖T‖ * theta
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    positivity
  have hr_lt : r < ‖T‖ := by
    dsimp [r]
    nlinarith
  rcases exists_unit_inner_gt_of_lt_norm (T := T) hT hr_nonneg hr_lt with
    ⟨x, hx_norm, hx_inner⟩
  have hr_pos : 0 < r := by
    dsimp [r]
    exact mul_pos hTnorm htheta_pos
  have hlog := Real.log_le_sub_one_of_pos hr_pos
  have hlog_r : Real.log r = Real.log ‖T‖ - a * eps := by
    dsimp [r, theta]
    rw [Real.log_mul hTnorm.ne' (Real.exp_ne_zero _), Real.log_exp]
    ring
  rw [hlog_r] at hlog
  refine ⟨x, hx_norm, ?_⟩
  calc
    (1 - inner ℝ (T x) x) / a < (1 - r) / a := by
      exact (div_lt_iff₀ ha).2 (by linarith)
    _ ≤ (-Real.log ‖T‖ + a * eps) / a := by
      exact (div_le_iff₀ ha).2 (by linarith)
    _ = -Real.log ‖T‖ / a + eps := by
      field_simp [ha.ne']
      <;> ring

end ContinuousLinearMap.IsPositive

end

end MathlibAnalytic
end MGAP4D
