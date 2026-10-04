import MGAP4D.MathlibAnalytic.GeometricTailIndexGrowth
import Mathlib.Tactic

/-!
# Square-root conversion from variance tails to geometric residual bounds

Projection and conditional-variance estimates naturally control squares of
Hilbert residuals.  The H1-C3 finite reconstruction receiver consumes residual
norms themselves.

For nonnegative geometric rates, taking square roots converts

  x_n^2 <= A * rho^n

into

  x_n <= sqrt(A) * sqrt(rho)^n.

Likewise a growing-distance variance tail

  x_n^2 <= C * rho^(D_n) / (1-rho)

with n <= D_n yields a scale-geometric residual bound with rate sqrt(rho).

This file is model-independent.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Square root commutes with natural powers on the nonnegative real axis. -/
theorem real_sqrt_pow_nat_of_nonneg
    (x : ℝ)
    (hx : 0 ≤ x)
    (n : ℕ) :
    Real.sqrt (x ^ n) = (Real.sqrt x) ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        Real.sqrt (x ^ (n + 1)) =
            Real.sqrt (x ^ n * x) := by
              rw [pow_succ]
        _ = Real.sqrt (x ^ n) * Real.sqrt x :=
          Real.sqrt_mul (pow_nonneg hx n) x
        _ = (Real.sqrt x) ^ n * Real.sqrt x := by
          rw [ih]
        _ = (Real.sqrt x) ^ (n + 1) := by
          rw [pow_succ]

/-- A square-geometric bound gives the corresponding geometric bound after
taking square roots. -/
theorem real_le_sqrt_coefficient_mul_sqrt_rate_pow_of_sq_le
    (x C rho : ℝ)
    (n : ℕ)
    (hC : 0 ≤ C)
    (hrho : 0 ≤ rho)
    (hsq : x ^ 2 ≤ C * rho ^ n) :
    x ≤ Real.sqrt C * (Real.sqrt rho) ^ n := by
  calc
    x ≤ Real.sqrt (C * rho ^ n) :=
      Real.le_sqrt_of_sq_le hsq
    _ = Real.sqrt C * Real.sqrt (rho ^ n) :=
      Real.sqrt_mul hC (rho ^ n)
    _ = Real.sqrt C * (Real.sqrt rho) ^ n := by
      rw [real_sqrt_pow_nat_of_nonneg rho hrho n]

/-- A growing-distance geometric upper bound on the square of a residual
converts directly to an ordinary scale-geometric bound on the residual itself.

The contraction rate changes from rho to sqrt(rho). -/
theorem real_le_sqrt_scale_geometric_of_sq_le_geometric_tail_of_index_le_distance
    (f : ℕ → ℝ)
    (distance : ℕ → ℕ)
    (C rho : ℝ)
    (hC : 0 ≤ C)
    (hrho0 : 0 ≤ rho)
    (hrho1 : rho < 1)
    (hDistance : ∀ n, n ≤ distance n)
    (hTailSq :
      ∀ n,
        (f n) ^ 2 ≤ C * (rho ^ distance n / (1 - rho))) :
    ∀ n,
      f n ≤
        Real.sqrt (C / (1 - rho)) *
          (Real.sqrt rho) ^ n := by
  intro n
  have hscale :
      (f n) ^ 2 ≤
        (C / (1 - rho)) * rho ^ n := by
    exact
      (hTailSq n).trans
        (real_geometric_tail_le_scale_geometric_of_index_le_distance
          C rho hC hrho0 hrho1 (hDistance n))
  have hden : 0 ≤ 1 - rho := sub_nonneg.mpr hrho1.le
  have hCdiv : 0 ≤ C / (1 - rho) := div_nonneg hC hden
  exact
    real_le_sqrt_coefficient_mul_sqrt_rate_pow_of_sq_le
      (f n) (C / (1 - rho)) rho n hCdiv hrho0 hscale

/-- The square-root of a nonnegative strict contraction rate remains a strict
contraction rate. -/
theorem real_sqrt_lt_one_of_nonneg_of_lt_one
    (rho : ℝ)
    (hrho0 : 0 ≤ rho)
    (hrho1 : rho < 1) :
    Real.sqrt rho < 1 := by
  have hsqrt0 := Real.sqrt_nonneg rho
  have hsq := Real.sq_sqrt hrho0
  nlinarith

end

end MathlibAnalytic
end MGAP4D
