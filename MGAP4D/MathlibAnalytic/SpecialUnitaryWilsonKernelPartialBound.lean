import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonKernelPartialLimit

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The normalized real-trace relative kernel of `SU(N)` has absolute value at
most one. -/
theorem specialUnitaryNormalizedTraceRelativeKernel_abs_le_one
    {N : ℕ}
    (hN : 0 < N)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    |specialUnitaryNormalizedTraceRelativeKernel N g h| ≤ 1 := by
  unfold specialUnitaryNormalizedTraceRelativeKernel
  exact abs_le.2 (normalizedSpecialUnitaryRealTrace_mem_Icc hN (g⁻¹ * h))

/-- If a scalar kernel has absolute value at most one, every nonnegative-scale
finite exponential partial kernel is bounded by the full scalar exponential. -/
theorem RealHilbertKernelFeature.exponentialPartialKernel_abs_le_exp
    {X : Type}
    (kernel : X → X → ℝ)
    (c : ℝ)
    (hc : 0 ≤ c)
    (n : ℕ)
    (x y : X)
    (hkernel : |kernel x y| ≤ 1) :
    |RealHilbertKernelFeature.exponentialPartialKernel kernel c n x y| ≤
      Real.exp c := by
  rw [RealHilbertKernelFeature.exponentialPartialKernel_eq_sum]
  calc
    |∑ m ∈ Finset.range (n + 1),
        (c * kernel x y) ^ m / (Nat.factorial m : ℝ)| ≤
        ∑ m ∈ Finset.range (n + 1),
          |(c * kernel x y) ^ m / (Nat.factorial m : ℝ)| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.range (n + 1),
        c ^ m / (Nat.factorial m : ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      rw [abs_div, abs_pow, abs_mul, abs_of_nonneg hc]
      rw [abs_of_nonneg (show 0 ≤ (Nat.factorial m : ℝ) by positivity)]
      have hbase : c * |kernel x y| ≤ c := by
        calc
          c * |kernel x y| ≤ c * 1 := mul_le_mul_of_nonneg_left hkernel hc
          _ = c := mul_one c
      have hpow : (c * |kernel x y|) ^ m ≤ c ^ m :=
        pow_le_pow_left₀ (mul_nonneg hc (abs_nonneg _)) hbase m
      exact div_le_div_of_nonneg_right hpow (by positivity)
    _ ≤ Real.exp c := Real.sum_le_exp_of_nonneg hc (n + 1)

/-- For nonnegative Wilson coupling, every finite Taylor approximation of the
relative `SU(N)` Wilson kernel has absolute value at most one. -/
theorem specialUnitaryWilsonRelativeKernelPartial_abs_le_one
    {N : ℕ}
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (degree : ℕ)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    |specialUnitaryWilsonRelativeKernelPartial N beta degree g h| ≤ 1 := by
  unfold specialUnitaryWilsonRelativeKernelPartial
  rw [abs_mul, Real.abs_exp]
  calc
    Real.exp (-beta) *
        |RealHilbertKernelFeature.exponentialPartialKernel
          (specialUnitaryNormalizedTraceRelativeKernel N) beta degree g h| ≤
      Real.exp (-beta) * Real.exp beta := by
        exact mul_le_mul_of_nonneg_left
          (RealHilbertKernelFeature.exponentialPartialKernel_abs_le_exp
            (specialUnitaryNormalizedTraceRelativeKernel N) beta hbeta degree g h
            (specialUnitaryNormalizedTraceRelativeKernel_abs_le_one hN g h))
          (Real.exp_nonneg _)
    _ = 1 := by rw [← Real.exp_add]; simp

end

end MathlibAnalytic
end MGAP4D
