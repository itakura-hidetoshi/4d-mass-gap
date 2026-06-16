import Mathlib.Analysis.InnerProductSpace.Spectrum

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A uniform quadratic-form lower bound for a finite-dimensional real
symmetric operator gives the same lower bound for every eigenvalue generated
by mathlib's spectral theorem. -/
theorem symmetric_eigenvalue_ge_of_quadratic_form_lower_bound
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {T : E →ₗ[ℝ] E}
    (hT : T.IsSymmetric)
    {n : ℕ}
    (hn : Module.finrank ℝ E = n)
    (δ : ℝ)
    (hLower : ∀ x : E, δ * ‖x‖ ^ 2 ≤ inner ℝ (T x) x)
    (i : Fin n) :
    δ ≤ hT.eigenvalues hn i := by
  simpa [hT.apply_eigenvectorBasis, real_inner_smul_left,
    inner_self_eq_norm_sq_to_K, OrthonormalBasis.norm_eq_one]
    using hLower (hT.eigenvectorBasis hn i)

end

end MathlibAnalytic
end MGAP4D
