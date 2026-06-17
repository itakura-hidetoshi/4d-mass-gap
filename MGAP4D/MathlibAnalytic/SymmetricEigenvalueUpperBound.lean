import Mathlib.Analysis.InnerProductSpace.Spectrum

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- If every eigenvalue of a finite-dimensional real symmetric operator is at
most `rho`, then its quadratic form is bounded above by `rho * ‖x‖²`.

This is the upper-bound companion to
`symmetric_eigenvalue_ge_of_quadratic_form_lower_bound`.  The proof uses
mathlib's orthonormal eigenbasis and sums the coordinatewise eigenvalue bounds. -/
theorem symmetric_quadraticForm_le_of_eigenvalues_le
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {T : E →ₗ[ℝ] E}
    (hT : T.IsSymmetric)
    {n : ℕ}
    (hn : Module.finrank ℝ E = n)
    (rho : ℝ)
    (hEigenvalue : ∀ i : Fin n, hT.eigenvalues hn i ≤ rho)
    (x : E) :
    inner ℝ (T x) x ≤ rho * ‖x‖ ^ 2 := by
  let b := hT.eigenvectorBasis hn
  have hDiagonal (i : Fin n) :
      b.repr (T x) i = hT.eigenvalues hn i * b.repr x i := by
    simpa [b] using hT.eigenvectorBasis_apply_self_apply hn x i
  calc
    inner ℝ (T x) x = inner ℝ (b.repr (T x)) (b.repr x) := by
      exact (b.repr.inner_map_map (T x) x).symm
    _ = ∑ i : Fin n,
        hT.eigenvalues hn i * (b.repr x i) ^ 2 := by
      rw [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [hDiagonal i]
      change
        b.repr x i * (hT.eigenvalues hn i * b.repr x i) =
          hT.eigenvalues hn i * (b.repr x i) ^ 2
      ring
    _ ≤ ∑ i : Fin n, rho * (b.repr x i) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      exact mul_le_mul_of_nonneg_right (hEigenvalue i) (sq_nonneg _)
    _ = rho * ‖x‖ ^ 2 := by
      rw [← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq]
      rw [b.repr.norm_map]

end

end MathlibAnalytic
end MGAP4D
