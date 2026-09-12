import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupIVPUniqueness

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The finite real diagonal Hamiltonian semigroup, based at an arbitrary initial
 time `t₀`, is the unique operator-norm solution of the left equation
 `U' = -H U` with `U t₀ = 1`.

The proof translates time so that `t₀` becomes zero and invokes the zero-time
left operator IVP uniqueness theorem. -/
theorem orthonormalDiagonalHamiltonianSemigroup_sub_eq_of_hasDerivAt_operator_left
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (t₀ : ℝ)
    (U : ℝ → (E →L[ℝ] E))
    (hU0 : U t₀ = 1)
    (hU : ∀ t : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U t) t) :
    U = fun t : ℝ => orthonormalDiagonalHamiltonianSemigroup b a (t - t₀) := by
  have hshift : ∀ r : ℝ,
      HasDerivAt (fun s : ℝ => U (s + t₀))
        ((-orthonormalDiagonalOperator b a) * U (r + t₀)) r := by
    intro r
    have h := (hU (r + t₀)).scomp r ((hasDerivAt_id' r).add_const t₀)
    simpa [Function.comp_def] using h
  have htranslated :=
    orthonormalDiagonalHamiltonianSemigroup_eq_of_hasDerivAt_operator_left
      b a (fun r : ℝ => U (r + t₀)) (by simpa using hU0) hshift
  funext t
  have hpoint := congrFun htranslated (t - t₀)
  simpa only [sub_add_cancel] using hpoint

/-- The finite real diagonal Hamiltonian semigroup, based at an arbitrary initial
 time `t₀`, is the unique operator-norm solution of the right equation
 `U' = U (-H)` with `U t₀ = 1`.

The proof translates time so that `t₀` becomes zero and invokes the zero-time
right operator IVP uniqueness theorem. -/
theorem orthonormalDiagonalHamiltonianSemigroup_sub_eq_of_hasDerivAt_operator_right
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (t₀ : ℝ)
    (U : ℝ → (E →L[ℝ] E))
    (hU0 : U t₀ = 1)
    (hU : ∀ t : ℝ,
      HasDerivAt U (U t * (-orthonormalDiagonalOperator b a)) t) :
    U = fun t : ℝ => orthonormalDiagonalHamiltonianSemigroup b a (t - t₀) := by
  have hshift : ∀ r : ℝ,
      HasDerivAt (fun s : ℝ => U (s + t₀))
        (U (r + t₀) * (-orthonormalDiagonalOperator b a)) r := by
    intro r
    have h := (hU (r + t₀)).scomp r ((hasDerivAt_id' r).add_const t₀)
    simpa [Function.comp_def] using h
  have htranslated :=
    orthonormalDiagonalHamiltonianSemigroup_eq_of_hasDerivAt_operator_right
      b a (fun r : ℝ => U (r + t₀)) (by simpa using hU0) hshift
  funext t
  have hpoint := congrFun htranslated (t - t₀)
  simpa only [sub_add_cancel] using hpoint

end

end MathlibAnalytic
end MGAP4D
