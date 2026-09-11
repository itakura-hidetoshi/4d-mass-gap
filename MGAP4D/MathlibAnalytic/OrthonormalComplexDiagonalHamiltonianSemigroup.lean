import MGAP4D.MathlibAnalytic.OrthonormalComplexDiagonalOperatorExpLog
import MGAP4D.MathlibAnalytic.OrthonormalComplexDiagonalOperatorOrder

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped ComplexOrder

/-- The explicit continuous-time semigroup diagonal in a finite complex
orthonormal basis, with mode energies `aᵢ`. -/
noncomputable def orthonormalComplexDiagonalHamiltonianSemigroup
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (b : OrthonormalBasis ι ℂ E)
    (a : ι → ℝ)
    (t : ℝ) : E →L[ℂ] E :=
  orthonormalComplexDiagonalOperator b (fun i => Real.exp (-(t * a i)))

/-- Time zero is the identity. -/
@[simp]
theorem orthonormalComplexDiagonalHamiltonianSemigroup_zero
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (b : OrthonormalBasis ι ℂ E)
    (a : ι → ℝ) :
    orthonormalComplexDiagonalHamiltonianSemigroup b a 0 = 1 := by
  unfold orthonormalComplexDiagonalHamiltonianSemigroup
  have hcoeff : (fun i => Real.exp (-((0 : ℝ) * a i))) = fun _ => 1 := by
    funext i
    simp
  rw [hcoeff, orthonormalComplexDiagonalOperator_one]

/-- The explicit diagonal family satisfies the semigroup addition law. -/
theorem orthonormalComplexDiagonalHamiltonianSemigroup_add
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (b : OrthonormalBasis ι ℂ E)
    (a : ι → ℝ)
    (s t : ℝ) :
    orthonormalComplexDiagonalHamiltonianSemigroup b a (s + t) =
      orthonormalComplexDiagonalHamiltonianSemigroup b a s *
        orthonormalComplexDiagonalHamiltonianSemigroup b a t := by
  unfold orthonormalComplexDiagonalHamiltonianSemigroup
  rw [orthonormalComplexDiagonalOperator_mul]
  congr 1
  funext i
  rw [← Real.exp_add]
  congr 1
  ring

/-- Time one has the transfer coefficients `exp (-aᵢ)`. -/
theorem orthonormalComplexDiagonalHamiltonianSemigroup_one
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (b : OrthonormalBasis ι ℂ E)
    (a : ι → ℝ) :
    orthonormalComplexDiagonalHamiltonianSemigroup b a 1 =
      orthonormalComplexDiagonalOperator b (fun i => Real.exp (-a i)) := by
  unfold orthonormalComplexDiagonalHamiltonianSemigroup
  congr 1
  funext i
  simp

/-- On every basis mode, time evolution multiplies by `exp (-t aᵢ)`. -/
theorem orthonormalComplexDiagonalHamiltonianSemigroup_apply_basis
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (b : OrthonormalBasis ι ℂ E)
    (a : ι → ℝ)
    (t : ℝ)
    (i : ι) :
    orthonormalComplexDiagonalHamiltonianSemigroup b a t (b i) =
      (Real.exp (-(t * a i)) : ℂ) • b i := by
  exact orthonormalComplexDiagonalOperator_apply_basis b
    (fun j => Real.exp (-(t * a j))) i

/-- The diagonal semigroup is the operator exponential of the negative
`t`-scaled diagonal Hamiltonian. -/
theorem normedSpace_exp_neg_scaled_orthonormalComplexDiagonalOperator
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    [CompleteSpace E]
    (b : OrthonormalBasis ι ℂ E)
    (a : ι → ℝ)
    (t : ℝ) :
    NormedSpace.exp
        (-orthonormalComplexDiagonalOperator b (fun i => t * a i)) =
      orthonormalComplexDiagonalHamiltonianSemigroup b a t := by
  simpa [orthonormalComplexDiagonalHamiltonianSemigroup] using
    (normedSpace_exp_neg_orthonormalComplexDiagonalOperator b
      (fun i => t * a i))

/-- Every time slice is positive. -/
theorem orthonormalComplexDiagonalHamiltonianSemigroup_isPositive
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (b : OrthonormalBasis ι ℂ E)
    (a : ι → ℝ)
    (t : ℝ) :
    (orthonormalComplexDiagonalHamiltonianSemigroup b a t).IsPositive := by
  unfold orthonormalComplexDiagonalHamiltonianSemigroup
  apply orthonormalComplexDiagonalOperator_isPositive
  intro i
  exact (Real.exp_pos _).le

/-- Every time slice is self-adjoint. -/
theorem orthonormalComplexDiagonalHamiltonianSemigroup_isSelfAdjoint
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (b : OrthonormalBasis ι ℂ E)
    (a : ι → ℝ)
    (t : ℝ) :
    IsSelfAdjoint (orthonormalComplexDiagonalHamiltonianSemigroup b a t) :=
  (orthonormalComplexDiagonalHamiltonianSemigroup_isPositive b a t).isSelfAdjoint

/-- Every time slice is nonnegative in the Loewner order. -/
theorem orthonormalComplexDiagonalHamiltonianSemigroup_nonneg
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (b : OrthonormalBasis ι ℂ E)
    (a : ι → ℝ)
    (t : ℝ) :
    0 ≤ orthonormalComplexDiagonalHamiltonianSemigroup b a t :=
  (ContinuousLinearMap.nonneg_iff_isPositive
    (orthonormalComplexDiagonalHamiltonianSemigroup b a t)).2
      (orthonormalComplexDiagonalHamiltonianSemigroup_isPositive b a t)

/-- For nonnegative time and nonnegative energies, every time slice is below the
identity, hence is a positive self-adjoint contraction in Loewner order. -/
theorem orthonormalComplexDiagonalHamiltonianSemigroup_le_one
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (b : OrthonormalBasis ι ℂ E)
    (a : ι → ℝ)
    (ha : ∀ i : ι, 0 ≤ a i)
    (t : ℝ)
    (ht : 0 ≤ t) :
    orthonormalComplexDiagonalHamiltonianSemigroup b a t ≤ 1 := by
  unfold orthonormalComplexDiagonalHamiltonianSemigroup
  rw [← orthonormalComplexDiagonalOperator_one b]
  apply orthonormalComplexDiagonalOperator_le
  intro i
  calc
    Real.exp (-(t * a i)) ≤ Real.exp 0 :=
      Real.exp_le_exp.mpr (neg_nonpos.mpr (mul_nonneg ht (ha i)))
    _ = 1 := Real.exp_zero

/-- For nonnegative time and nonnegative energies, every time slice belongs to
`[0,I]`. -/
theorem orthonormalComplexDiagonalHamiltonianSemigroup_mem_Icc
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (b : OrthonormalBasis ι ℂ E)
    (a : ι → ℝ)
    (ha : ∀ i : ι, 0 ≤ a i)
    (t : ℝ)
    (ht : 0 ≤ t) :
    orthonormalComplexDiagonalHamiltonianSemigroup b a t ∈
      Set.Icc (0 : E →L[ℂ] E) 1 :=
  ⟨orthonormalComplexDiagonalHamiltonianSemigroup_nonneg b a t,
    orthonormalComplexDiagonalHamiltonianSemigroup_le_one b a ha t ht⟩

/-- A uniform lower bound `δ ≤ aᵢ` gives the exact semigroup decay bound
`Sₜ ≤ exp (-tδ) I` for nonnegative time. -/
theorem orthonormalComplexDiagonalHamiltonianSemigroup_le_exp_neg_lowerBound
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (b : OrthonormalBasis ι ℂ E)
    (a : ι → ℝ)
    (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i)
    (t : ℝ)
    (ht : 0 ≤ t) :
    orthonormalComplexDiagonalHamiltonianSemigroup b a t ≤
      algebraMap ℝ (E →L[ℂ] E) (Real.exp (-(t * δ))) := by
  unfold orthonormalComplexDiagonalHamiltonianSemigroup
  rw [← orthonormalComplexDiagonalOperator_const_eq_algebraMap b
    (Real.exp (-(t * δ)))]
  apply orthonormalComplexDiagonalOperator_le
  intro i
  exact Real.exp_le_exp.mpr
    (neg_le_neg (mul_le_mul_of_nonneg_left (hδ i) ht))

end

end MathlibAnalytic
end MGAP4D
