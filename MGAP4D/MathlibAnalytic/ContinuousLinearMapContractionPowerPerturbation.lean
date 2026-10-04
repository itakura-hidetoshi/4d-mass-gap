import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorJetLocallyUniformMatrixElementLimit
import Mathlib.Tactic

/-!
# Contraction power perturbation bounds

The SU(2) cross-scale Krylov route now reduces strong-limit existence to
quantitative control of adjacent finite transfer dynamics.

This file packages the generic operator estimate needed for that comparison.

For real bounded operators A and B with operator norm at most one,

  ||A^m - B^m|| <= m ||A - B||.

Consequently, if ||y|| <= 1,

  ||A^m x - B^m y||
    <= ||x - y|| + m ||A - B||.

No commutativity is assumed.  The first estimate is a q=1 corollary of the
existing noncommutative power-difference theorem; the second separates initial
vector mismatch from operator mismatch.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Natural powers of a contraction remain contractions in operator norm. -/
theorem continuousLinearMap_pow_norm_le_one_of_norm_le_one
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E)
    (hA : ‖A‖ ≤ 1)
    (m : ℕ) :
    ‖A ^ m‖ ≤ 1 := by
  cases m with
  | zero =>
      simp
  | succ n =>
      calc
        ‖A ^ (n + 1)‖ ≤ ‖A‖ ^ (n + 1) :=
          norm_pow_le' A (by omega)
        _ ≤ (1 : ℝ) ^ (n + 1) :=
          pow_le_pow_left₀ (norm_nonneg A) hA (n + 1)
        _ = 1 := one_pow _

/-- Noncommutative contraction powers are Lipschitz in the operator with
constant equal to the natural time. -/
theorem continuousLinearMap_pow_sub_pow_norm_le_nat
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B : E →L[ℝ] E)
    (hA : ‖A‖ ≤ 1)
    (hB : ‖B‖ ≤ 1)
    (m : ℕ) :
    ‖A ^ m - B ^ m‖ ≤ (m : ℝ) * ‖A - B‖ := by
  cases m with
  | zero =>
      simp
  | succ n =>
      have h :=
        continuousLinearMap_pow_succ_sub_pow_succ_norm_le
          A B (q := (1 : ℝ)) zero_le_one hA hB n
      simpa [Nat.cast_succ] using h

/-- Perturbation bound for contraction powers acting on two nearby vectors.

The first term is the initial-vector mismatch; the second is the accumulated
operator mismatch. -/
theorem continuousLinearMap_contraction_pow_apply_sub_pow_apply_norm_le
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B : E →L[ℝ] E)
    (hA : ‖A‖ ≤ 1)
    (hB : ‖B‖ ≤ 1)
    (m : ℕ)
    (x y : E)
    (hy : ‖y‖ ≤ 1) :
    ‖(A ^ m) x - (B ^ m) y‖ ≤
      ‖x - y‖ + (m : ℝ) * ‖A - B‖ := by
  have hdecomp :
      (A ^ m) x - (B ^ m) y =
        (A ^ m) (x - y) + (A ^ m - B ^ m) y := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    abel
  rw [hdecomp]
  have hApow :
      ‖A ^ m‖ ≤ 1 :=
    continuousLinearMap_pow_norm_le_one_of_norm_le_one A hA m
  have hdiff :
      ‖A ^ m - B ^ m‖ ≤ (m : ℝ) * ‖A - B‖ :=
    continuousLinearMap_pow_sub_pow_norm_le_nat A B hA hB m
  calc
    ‖(A ^ m) (x - y) + (A ^ m - B ^ m) y‖ ≤
        ‖(A ^ m) (x - y)‖ + ‖(A ^ m - B ^ m) y‖ :=
      norm_add_le _ _
    _ ≤
        ‖A ^ m‖ * ‖x - y‖ +
          ‖A ^ m - B ^ m‖ * ‖y‖ := by
      exact add_le_add
        ((A ^ m).le_opNorm (x - y))
        ((A ^ m - B ^ m).le_opNorm y)
    _ ≤
        1 * ‖x - y‖ +
          ((m : ℝ) * ‖A - B‖) * 1 := by
      apply add_le_add
      · exact
          mul_le_mul_of_nonneg_right hApow
            (norm_nonneg (x - y))
      · exact
          mul_le_mul hdiff hy
            (norm_nonneg y)
            (mul_nonneg (Nat.cast_nonneg m) (norm_nonneg (A - B)))
    _ = ‖x - y‖ + (m : ℝ) * ‖A - B‖ := by
      ring

end

end MathlibAnalytic
end MGAP4D
