import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Convert geometric decay in a growing distance to geometric decay in scale

Finite-volume locality and Dobrushin estimates naturally produce bounds of the
form

  f_n <= C * rho^(D_n) / (1-rho),

where `D_n` is a support-separation distance.  The H1-C3 reconstruction
receivers are indexed by the refinement scale `n`.

For `0 <= rho < 1`, powers are antitone in the natural exponent.  Therefore
any quantitative distance growth

  n <= D_n

converts the locality tail directly to

  f_n <= (C / (1-rho)) * rho^n.

This file keeps that elementary conversion model-independent so that finite
Wilson influence/covariance estimates can feed the reconstruction receivers
without repeating scalar arithmetic.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- For a real contraction factor in `[0,1]`, natural powers decrease as the
exponent increases. -/
theorem real_pow_antitone_nat_of_nonneg_of_le_one
    (rho : ℝ)
    (hrho0 : 0 ≤ rho)
    (hrho1 : rho ≤ 1)
    {m n : ℕ}
    (hmn : m ≤ n) :
    rho ^ n ≤ rho ^ m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have hk : rho ^ k ≤ 1 := by
    induction k with
    | zero =>
        simp
    | succ k ih =>
        rw [pow_succ]
        calc
          rho ^ k * rho ≤ 1 * 1 :=
            mul_le_mul ih hrho1 hrho0 zero_le_one
          _ = 1 := by norm_num
  rw [pow_add]
  calc
    rho ^ m * rho ^ k ≤ rho ^ m * 1 :=
      mul_le_mul_of_nonneg_left hk (pow_nonneg hrho0 m)
    _ = rho ^ m := by rw [mul_one]

/-- A geometric tail beginning at a distance `D >= n` is bounded by the
corresponding geometric scale envelope. -/
theorem real_geometric_tail_le_scale_geometric_of_index_le_distance
    (C rho : ℝ)
    (hC : 0 ≤ C)
    (hrho0 : 0 ≤ rho)
    (hrho1 : rho < 1)
    {n D : ℕ}
    (hDistance : n ≤ D) :
    C * (rho ^ D / (1 - rho)) ≤
      (C / (1 - rho)) * rho ^ n := by
  have hden : 0 < 1 - rho := sub_pos.mpr hrho1
  have hpow : rho ^ D ≤ rho ^ n :=
    real_pow_antitone_nat_of_nonneg_of_le_one
      rho hrho0 hrho1.le hDistance
  calc
    C * (rho ^ D / (1 - rho)) ≤
        C * (rho ^ n / (1 - rho)) := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hpow hden.le)
        hC
    _ = (C / (1 - rho)) * rho ^ n := by
      ring

/-- Pointwise locality tails with distance at least the scale index become an
ordinary geometric bound in the scale index. -/
theorem le_scale_geometric_of_le_geometric_tail_of_index_le_distance
    (f : ℕ → ℝ)
    (distance : ℕ → ℕ)
    (C rho : ℝ)
    (hC : 0 ≤ C)
    (hrho0 : 0 ≤ rho)
    (hrho1 : rho < 1)
    (hDistance : ∀ n, n ≤ distance n)
    (hTail :
      ∀ n,
        f n ≤ C * (rho ^ distance n / (1 - rho))) :
    ∀ n,
      f n ≤ (C / (1 - rho)) * rho ^ n := by
  intro n
  exact
    (hTail n).trans
      (real_geometric_tail_le_scale_geometric_of_index_le_distance
        C rho hC hrho0 hrho1 (hDistance n))

/-- Nonnegative sequences controlled by a growing-distance geometric tail are
summable once the distance dominates the refinement index. -/
theorem summable_of_nonneg_of_le_geometric_tail_of_index_le_distance
    (f : ℕ → ℝ)
    (distance : ℕ → ℕ)
    (C rho : ℝ)
    (hf : ∀ n, 0 ≤ f n)
    (hC : 0 ≤ C)
    (hrho0 : 0 ≤ rho)
    (hrho1 : rho < 1)
    (hDistance : ∀ n, n ≤ distance n)
    (hTail :
      ∀ n,
        f n ≤ C * (rho ^ distance n / (1 - rho))) :
    Summable f := by
  have hmajorant :
      Summable (fun n : ℕ => (C / (1 - rho)) * rho ^ n) :=
    (summable_geometric_of_lt_one hrho0 hrho1).mul_left
      (C / (1 - rho))
  exact
    Summable.of_nonneg_of_le
      hf
      (le_scale_geometric_of_le_geometric_tail_of_index_le_distance
        f distance C rho hC hrho0 hrho1 hDistance hTail)
      hmajorant

end

end MathlibAnalytic
end MGAP4D
