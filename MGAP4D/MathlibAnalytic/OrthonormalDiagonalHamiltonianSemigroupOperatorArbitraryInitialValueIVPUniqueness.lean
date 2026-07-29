import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupIVPUniqueness

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- For an arbitrary initial operator `A` at time `t₀`, the unique operator-norm
solution of the left equation `U' = -H U` is `S (t - t₀) A`.

No invertibility assumption on `A` is required. -/
theorem orthonormalDiagonalHamiltonianSemigroup_sub_mul_eq_of_hasDerivAt_operator_left
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (t₀ : ℝ)
    (A : E →L[ℝ] E)
    (U : ℝ → (E →L[ℝ] E))
    (hU0 : U t₀ = A)
    (hU : ∀ t : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U t) t) :
    U = fun t : ℝ =>
      orthonormalDiagonalHamiltonianSemigroup b a (t - t₀) * A := by
  funext t
  let S := orthonormalDiagonalHamiltonianSemigroup b a
  let H := orthonormalDiagonalOperator b a
  have hSneg (s : ℝ) :
      HasDerivAt (fun r : ℝ => S (-(r - t₀)))
        (H * S (-(s - t₀))) s := by
    have h :=
      (orthonormalDiagonalHamiltonianSemigroup_hasDerivAt_operator_left
        b a (-(s - t₀))).scomp s (((hasDerivAt_id' s).sub_const t₀).neg)
    simpa [Function.comp_def, S, H] using h
  have hprod (s : ℝ) :
      HasDerivAt (fun r : ℝ => S (-(r - t₀)) * U r) 0 s := by
    convert (hSneg s).mul (hU s) using 1
    rw [orthonormalDiagonalHamiltonianSemigroup_commutes_hamiltonian_explicit
      b a (-(s - t₀))]
    noncomm_ring
  have hdiff : Differentiable ℝ (fun r : ℝ => S (-(r - t₀)) * U r) :=
    fun s => (hprod s).differentiableAt
  have hzero : ∀ s : ℝ, deriv (fun r : ℝ => S (-(r - t₀)) * U r) s = 0 :=
    fun s => (hprod s).deriv
  have hconst := is_const_of_deriv_eq_zero hdiff hzero t t₀
  have hintegrating : S (-(t - t₀)) * U t = A := by
    simpa [S, hU0] using hconst
  calc
    U t = (S (t - t₀) * S (-(t - t₀))) * U t := by
      rw [← orthonormalDiagonalHamiltonianSemigroup_add b a (t - t₀) (-(t - t₀))]
      simp
    _ = S (t - t₀) * (S (-(t - t₀)) * U t) := by rw [mul_assoc]
    _ = S (t - t₀) * A := by rw [hintegrating]
    _ = orthonormalDiagonalHamiltonianSemigroup b a (t - t₀) * A := rfl

/-- For an arbitrary initial operator `A` at time `t₀`, the unique operator-norm
solution of the right equation `U' = U (-H)` is `A S (t - t₀)`.

No invertibility assumption on `A` is required. -/
theorem orthonormalDiagonalHamiltonianSemigroup_mul_sub_eq_of_hasDerivAt_operator_right
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (t₀ : ℝ)
    (A : E →L[ℝ] E)
    (U : ℝ → (E →L[ℝ] E))
    (hU0 : U t₀ = A)
    (hU : ∀ t : ℝ,
      HasDerivAt U (U t * (-orthonormalDiagonalOperator b a)) t) :
    U = fun t : ℝ =>
      A * orthonormalDiagonalHamiltonianSemigroup b a (t - t₀) := by
  funext t
  let S := orthonormalDiagonalHamiltonianSemigroup b a
  let H := orthonormalDiagonalOperator b a
  have hSneg (s : ℝ) :
      HasDerivAt (fun r : ℝ => S (-(r - t₀)))
        (H * S (-(s - t₀))) s := by
    have h :=
      (orthonormalDiagonalHamiltonianSemigroup_hasDerivAt_operator_left
        b a (-(s - t₀))).scomp s (((hasDerivAt_id' s).sub_const t₀).neg)
    simpa [Function.comp_def, S, H] using h
  have hprod (s : ℝ) :
      HasDerivAt (fun r : ℝ => U r * S (-(r - t₀))) 0 s := by
    convert (hU s).mul (hSneg s) using 1
    noncomm_ring
  have hdiff : Differentiable ℝ (fun r : ℝ => U r * S (-(r - t₀))) :=
    fun s => (hprod s).differentiableAt
  have hzero : ∀ s : ℝ, deriv (fun r : ℝ => U r * S (-(r - t₀))) s = 0 :=
    fun s => (hprod s).deriv
  have hconst := is_const_of_deriv_eq_zero hdiff hzero t t₀
  have hintegrating : U t * S (-(t - t₀)) = A := by
    simpa [S, hU0] using hconst
  calc
    U t = U t * (S (-(t - t₀)) * S (t - t₀)) := by
      rw [← orthonormalDiagonalHamiltonianSemigroup_add b a (-(t - t₀)) (t - t₀)]
      simp
    _ = (U t * S (-(t - t₀))) * S (t - t₀) := by rw [← mul_assoc]
    _ = A * S (t - t₀) := by rw [hintegrating]
    _ = A * orthonormalDiagonalHamiltonianSemigroup b a (t - t₀) := rfl

end

end MathlibAnalytic
end MGAP4D
