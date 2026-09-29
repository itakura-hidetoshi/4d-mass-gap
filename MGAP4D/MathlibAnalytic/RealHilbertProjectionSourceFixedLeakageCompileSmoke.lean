import MGAP4D.MathlibAnalytic.RealHilbertProjectionSourceFixedLeakage

namespace MGAP4D.MathlibAnalytic

open scoped InnerProductSpace

#check realHilbertProjection_targetResidual_sq_eq_inner_residual_add_sourceLeakage
#check realHilbertProjection_targetResidual_norm_le_add_sourceResidual_of_leakage

-- Regression: positive-factor cancellation is an implication, not `mul_le_mul_left.mp`.
example (a b : ℝ) (ha : 0 < a) (h : a ^ 2 ≤ a * b) : a ≤ b := by
  exact _root_.le_of_mul_le_mul_left (by simpa only [pow_two] using h) ha

-- A genuinely commuting pair recovers coefficient-zero nonexpansiveness.
-- No positive-beta commutativity is inferred by the general theorem.
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P Q : E →L[ℝ] E)
    (hPIdem : P.comp P = P) (hQIdem : Q.comp Q = Q)
    (hPSymm : ∀ u v : E, inner ℝ (P u) v = inner ℝ u (P v))
    (hQSymm : ∀ u v : E, inner ℝ (Q u) v = inner ℝ u (Q v))
    (hComm : ∀ u : E, P (Q u) = Q (P u)) (x : E) :
    ‖Q x - P (Q x)‖ ≤ ‖x - P x‖ := by
  have hQApply : Q (Q x) = Q x := by
    simpa only [ContinuousLinearMap.comp_apply] using
      congrArg (fun T : E →L[ℝ] E => T x) hQIdem
  have hFixed : Q (P (Q x)) = P (Q x) := by
    calc
      Q (P (Q x)) = P (Q (Q x)) := (hComm (Q x)).symm
      _ = P (Q x) := congrArg (fun z => P z) hQApply
  have hLeakage : ‖P (Q x) - Q (P (Q x))‖ ≤ (0 : ℝ) * ‖Q x - P (Q x)‖ := by
    rw [hFixed, sub_self, norm_zero, zero_mul]
  simpa only [zero_mul, add_zero] using
    realHilbertProjection_targetResidual_norm_le_add_sourceResidual_of_leakage
      P Q hPIdem hQIdem hPSymm hQSymm 0 le_rfl x hLeakage

-- The zero-updated-residual branch does not divide by its norm.
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P Q : E →L[ℝ] E) (k : ℝ) (hk : 0 ≤ k) (x : E)
    (hFixed : P (Q x) = Q x) :
    ‖Q x - P (Q x)‖ ≤ ‖x - P x‖ + k * ‖x - Q x‖ := by
  rw [hFixed, sub_self, norm_zero]
  exact add_nonneg (norm_nonneg _) (mul_nonneg hk (norm_nonneg _))

end MGAP4D.MathlibAnalytic
