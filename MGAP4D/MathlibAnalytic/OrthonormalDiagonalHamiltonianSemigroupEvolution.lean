import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupGenerator

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open InnerProductSpace

/-- The scalar mode factor `exp (-t a)` has derivative
`(-a) exp (-t a)` at every time. -/
theorem real_exp_neg_mul_hasDerivAt_realSemigroup (a t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-(s * a)))
      ((-a) * Real.exp (-(t * a))) t := by
  have hmul : HasDerivAt (fun s : ℝ => s * a) a t := by
    simpa using (hasDerivAt_id' t).mul_const a
  have hneg : HasDerivAt (fun s : ℝ => -(s * a)) (-a) t := hmul.neg
  simpa [mul_comm] using hneg.exp

/-- In operator norm, the finite real diagonal Hamiltonian semigroup solves the
left evolution equation `S'_t = -H S_t` at every time. -/
theorem orthonormalDiagonalHamiltonianSemigroup_hasDerivAt_operator_left
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (t : ℝ) :
    HasDerivAt
      (orthonormalDiagonalHamiltonianSemigroup b a)
      ((-orthonormalDiagonalOperator b a) *
        orthonormalDiagonalHamiltonianSemigroup b a t) t := by
  have hrepr :
      orthonormalDiagonalHamiltonianSemigroup b a =
        fun s : ℝ =>
          ∑ i : ι, Real.exp (-(s * a i)) • rankOne ℝ (b i) (b i) := by
    funext s
    exact orthonormalDiagonalOperator_eq_sum_rankOne b
      (fun i => Real.exp (-(s * a i)))
  rw [hrepr]
  have hsum :
      HasDerivAt
        (fun s : ℝ =>
          ∑ i : ι, Real.exp (-(s * a i)) • rankOne ℝ (b i) (b i))
        (∑ i : ι,
          ((-a i) * Real.exp (-(t * a i))) • rankOne ℝ (b i) (b i)) t := by
    simpa using
      (HasDerivAt.fun_sum (u := Finset.univ) (x := t)
        (A := fun i s =>
          Real.exp (-(s * a i)) • rankOne ℝ (b i) (b i))
        (A' := fun i =>
          ((-a i) * Real.exp (-(t * a i))) • rankOne ℝ (b i) (b i))
        (fun i hi =>
          (real_exp_neg_mul_hasDerivAt_realSemigroup (a i) t).smul_const
            (rankOne ℝ (b i) (b i))))
  have hderiv :
      (∑ i : ι,
          ((-a i) * Real.exp (-(t * a i))) • rankOne ℝ (b i) (b i)) =
        (-orthonormalDiagonalOperator b a) *
          orthonormalDiagonalHamiltonianSemigroup b a t := by
    rw [show -orthonormalDiagonalOperator b a =
        orthonormalDiagonalOperator b (fun i => -a i) by
      rw [orthonormalDiagonalOperator_eq_sum_rankOne,
        orthonormalDiagonalOperator_eq_sum_rankOne, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      module]
    unfold orthonormalDiagonalHamiltonianSemigroup
    rw [orthonormalDiagonalOperator_mul,
      orthonormalDiagonalOperator_eq_sum_rankOne]
  rw [← hderiv]
  exact hsum

/-- The same derivative also satisfies the right evolution equation
`S'_t = S_t (-H)`. -/
theorem orthonormalDiagonalHamiltonianSemigroup_hasDerivAt_operator_right
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (t : ℝ) :
    HasDerivAt
      (orthonormalDiagonalHamiltonianSemigroup b a)
      (orthonormalDiagonalHamiltonianSemigroup b a t *
        (-orthonormalDiagonalOperator b a)) t := by
  convert orthonormalDiagonalHamiltonianSemigroup_hasDerivAt_operator_left b a t using 1
  unfold orthonormalDiagonalHamiltonianSemigroup
  rw [show -orthonormalDiagonalOperator b a =
      orthonormalDiagonalOperator b (fun i => -a i) by
    rw [orthonormalDiagonalOperator_eq_sum_rankOne,
      orthonormalDiagonalOperator_eq_sum_rankOne, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    module]
  rw [orthonormalDiagonalOperator_mul, orthonormalDiagonalOperator_mul]
  congr 1
  funext i
  ring

/-- Statewise form of the all-time evolution equation. -/
theorem orthonormalDiagonalHamiltonianSemigroup_hasDerivAt
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (t : ℝ)
    (x : E) :
    HasDerivAt
      (fun s : ℝ => orthonormalDiagonalHamiltonianSemigroup b a s x)
      (-(orthonormalDiagonalOperator b a
        (orthonormalDiagonalHamiltonianSemigroup b a t x))) t := by
  have h :=
    (orthonormalDiagonalHamiltonianSemigroup_hasDerivAt_operator_left b a t).clm_apply
      (hasDerivAt_const t x)
  simpa using h

/-- Ordinary derivative form of the all-time strong evolution equation. -/
theorem orthonormalDiagonalHamiltonianSemigroup_deriv
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (t : ℝ)
    (x : E) :
    deriv (fun s : ℝ => orthonormalDiagonalHamiltonianSemigroup b a s x) t =
      -(orthonormalDiagonalOperator b a
        (orthonormalDiagonalHamiltonianSemigroup b a t x)) :=
  (orthonormalDiagonalHamiltonianSemigroup_hasDerivAt b a t x).deriv

end

end MathlibAnalytic
end MGAP4D
