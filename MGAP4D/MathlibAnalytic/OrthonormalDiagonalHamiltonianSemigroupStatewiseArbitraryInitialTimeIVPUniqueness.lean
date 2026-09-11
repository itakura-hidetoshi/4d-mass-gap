import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupStatewiseIVPUniqueness

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The finite real diagonal Hamiltonian semigroup orbit through `x`, based at an
arbitrary initial time `t₀`, is the unique statewise solution of `u' = -H u`.

The proof translates time so that `t₀` becomes zero and invokes the zero-time
statewise IVP uniqueness theorem. -/
theorem orthonormalDiagonalHamiltonianSemigroup_apply_sub_eq_of_hasDerivAt
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (t₀ : ℝ)
    (x : E)
    (u : ℝ → E)
    (hu0 : u t₀ = x)
    (hu : ∀ t : ℝ,
      HasDerivAt u (-(orthonormalDiagonalOperator b a (u t))) t) :
    u = fun t : ℝ =>
      orthonormalDiagonalHamiltonianSemigroup b a (t - t₀) x := by
  have hshift : ∀ r : ℝ,
      HasDerivAt (fun s : ℝ => u (s + t₀))
        (-(orthonormalDiagonalOperator b a (u (r + t₀)))) r := by
    intro r
    have h := (hu (r + t₀)).scomp r ((hasDerivAt_id' r).add_const t₀)
    simpa [Function.comp_def] using h
  have htranslated :=
    orthonormalDiagonalHamiltonianSemigroup_apply_eq_of_hasDerivAt
      b a x (fun r : ℝ => u (r + t₀)) (by simpa using hu0) hshift
  funext t
  have hpoint := congrFun htranslated (t - t₀)
  simpa only [sub_add_cancel] using hpoint

end

end MathlibAnalytic
end MGAP4D
