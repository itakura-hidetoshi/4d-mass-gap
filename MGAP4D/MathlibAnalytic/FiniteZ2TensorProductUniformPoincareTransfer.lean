import MGAP4D.MathlibAnalytic.FiniteZ2TensorProductUniformPoincareInduction
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

/-- Constant-one vector on a finite Euclidean boundary space. -/
noncomputable def finiteBoundaryConstantOne
    {α : Type} [Fintype α] :
    FiniteBoundaryHilbert α :=
  WithLp.toLp 2 fun _ : α => 1

@[simp] theorem finiteBoundaryConstantOne_apply
    {α : Type} [Fintype α]
    (x : α) :
    finiteBoundaryConstantOne x = 1 :=
  rfl

/-- Finite function mass is the inner product against the constant vector. -/
theorem finiteFunctionMass_eq_inner_constantOne
    {α : Type} [Fintype α]
    (f : FiniteBoundaryHilbert α) :
    finiteFunctionMass f =
      inner ℝ f finiteBoundaryConstantOne := by
  rw [RCLike.inner_eq_wInner_one]
  simp [finiteFunctionMass, RCLike.wInner, finiteBoundaryConstantOne]

/-- The explicit finite squared sum is the Hilbert norm squared. -/
theorem finiteFunctionNormSq_eq_norm_sq
    {α : Type} [Fintype α]
    (f : FiniteBoundaryHilbert α) :
    finiteFunctionNormSq f = ‖f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, RCLike.inner_eq_wInner_one]
  simp [finiteFunctionNormSq, RCLike.wInner, pow_two]

/-- The finite-function kernel quadratic form is exactly the Euclidean
transfer Rayleigh form. -/
theorem finiteFunctionKernelQuadratic_eq_inner_operator
    {α : Type} [Fintype α]
    (kernel : α → α → ℝ)
    (f : FiniteBoundaryHilbert α) :
    finiteFunctionKernelQuadratic kernel f =
      inner ℝ (finiteKernelOperator kernel f) f := by
  exact (finiteKernelOperator_matrixElement kernel f f).symm

/-- The normalized Boolean product kernel remains symmetric in every tensor
dimension. -/
theorem finiteZ2NormalizedProductKernel_symmetric
    (q : ℝ) (n : ℕ)
    (A B : Fin n → Bool) :
    finiteZ2NormalizedProductKernel q n A B =
      finiteZ2NormalizedProductKernel q n B A := by
  rw [finiteZ2NormalizedProductKernel_apply,
    finiteZ2NormalizedProductKernel_apply]
  apply Finset.prod_congr rfl
  intro i _hi
  exact finiteZ2NormalizedLocalKernel_symmetric q (A i) (B i)

/-- Every column of the normalized Boolean product kernel has total mass one. -/
theorem finiteZ2NormalizedProductKernel_row_sum
    (q : ℝ) (n : ℕ)
    (B : Fin n → Bool) :
    ∑ A : Fin n → Bool,
      finiteZ2NormalizedProductKernel q n A B = 1 := by
  induction n with
  | zero =>
      simp [finiteZ2NormalizedProductKernel_apply]
  | succ n ih =>
      let e := finSuccFunctionEquiv Bool n
      rcases hB : e B with ⟨b, Bt⟩
      have hBrepr : B = e.symm (b, Bt) := by
        have h := e.symm_apply_apply B
        rw [hB] at h
        exact h.symm
      calc
        (∑ A : Fin (n + 1) → Bool,
            finiteZ2NormalizedProductKernel q (n + 1) A B) =
          ∑ p : Bool × (Fin n → Bool),
            finiteZ2NormalizedProductKernel q (n + 1)
              (e.symm p) (e.symm (b, Bt)) := by
            rw [hBrepr]
            refine Fintype.sum_equiv e _ _ ?_
            intro A
            simp
        _ = ∑ a : Bool, ∑ A : Fin n → Bool,
            finiteZ2NormalizedLocalKernel q a b *
              finiteZ2NormalizedProductKernel q n A Bt := by
            rw [Fintype.sum_prod_type]
            apply Finset.sum_congr rfl
            intro a _ha
            apply Finset.sum_congr rfl
            intro A _hA
            simp [e, finSuccFunctionEquiv,
              finiteZ2NormalizedProductKernel_succ_apply]
        _ = (∑ a : Bool, finiteZ2NormalizedLocalKernel q a b) *
            (∑ A : Fin n → Bool,
              finiteZ2NormalizedProductKernel q n A Bt) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro a _ha
            rw [Finset.mul_sum]
        _ = 1 := by
            rw [finiteZ2NormalizedLocalKernel_row_sum, ih, one_mul]

/-- The product transfer fixes the constant mode. -/
theorem finiteZ2NormalizedProductKernel_operator_constantOne
    (q : ℝ) (n : ℕ) :
    finiteKernelOperator (finiteZ2NormalizedProductKernel q n)
        finiteBoundaryConstantOne =
      finiteBoundaryConstantOne := by
  ext B
  rw [finiteKernelOperator_apply]
  simp only [finiteBoundaryConstantOne_apply, mul_one]
  exact finiteZ2NormalizedProductKernel_row_sum q n B

/-- The product-kernel Euclidean transfer is symmetric. -/
theorem finiteZ2NormalizedProductKernel_operator_isSymmetric
    (q : ℝ) (n : ℕ) :
    (finiteKernelOperator
      (finiteZ2NormalizedProductKernel q n)).toLinearMap.IsSymmetric :=
  finiteKernelOperator_isSymmetric _
    (finiteZ2NormalizedProductKernel_symmetric q n)

/-- The raw product transfer has operator norm at most one whenever the local
sign eigenvalue lies in `[0,1]`. -/
theorem finiteZ2NormalizedProductKernel_operator_norm_le_one
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (n : ℕ) :
    ‖finiteKernelOperator (finiteZ2NormalizedProductKernel q n)‖ ≤ 1 := by
  let T := finiteKernelOperator (finiteZ2NormalizedProductKernel q n)
  have hsymm : T.toLinearMap.IsSymmetric :=
    finiteZ2NormalizedProductKernel_operator_isSymmetric q n
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient T hsymm]
  apply ciSup_le
  intro f
  by_cases hf : f = 0
  · simp [hf]
  · have hinterval :=
      finiteZ2NormalizedProductKernel_quadratic_mem_normInterval
        hq0 hq1 n f
    have hquadratic :
        finiteFunctionKernelQuadratic
            (finiteZ2NormalizedProductKernel q n) f =
          inner ℝ (T f) f := by
      exact finiteFunctionKernelQuadratic_eq_inner_operator _ f
    have hnorm : finiteFunctionNormSq f = ‖f‖ ^ 2 :=
      finiteFunctionNormSq_eq_norm_sq f
    have hden : 0 < ‖f‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hf)
    have hnonneg : 0 ≤ T.rayleighQuotient f := by
      change 0 ≤ inner ℝ (T f) f / ‖f‖ ^ 2
      apply div_nonneg
      · simpa [← hquadratic] using hinterval.1
      · exact hden.le
    have hle : T.rayleighQuotient f ≤ 1 := by
      change inner ℝ (T f) f / ‖f‖ ^ 2 ≤ 1
      rw [div_le_one hden]
      simpa [← hquadratic, ← hnorm] using hinterval.2
    simpa [abs_of_nonneg hnonneg] using hle

/-- The raw product transfer has operator norm at least one because it fixes a
nonzero constant vector. -/
theorem finiteZ2NormalizedProductKernel_operator_one_le_norm
    (q : ℝ) (n : ℕ) :
    1 ≤ ‖finiteKernelOperator (finiteZ2NormalizedProductKernel q n)‖ := by
  let T := finiteKernelOperator (finiteZ2NormalizedProductKernel q n)
  let one : FiniteBoundaryHilbert (Fin n → Bool) := finiteBoundaryConstantOne
  have hone : one ≠ 0 := by
    intro hzero
    have hvalue := congrArg
      (fun f : FiniteBoundaryHilbert (Fin n → Bool) => f default) hzero
    simp [one, finiteBoundaryConstantOne] at hvalue
  have hfix : T one = one :=
    finiteZ2NormalizedProductKernel_operator_constantOne q n
  have hbound := T.le_opNorm one
  rw [hfix] at hbound
  have honeNorm : 0 < ‖one‖ := norm_pos_iff.mpr hone
  nlinarith [norm_nonneg T]

/-- The stochastic symmetric positive product transfer has exact operator norm
one in every tensor dimension. -/
theorem finiteZ2NormalizedProductKernel_operator_norm_eq_one
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (n : ℕ) :
    ‖finiteKernelOperator (finiteZ2NormalizedProductKernel q n)‖ = 1 :=
  le_antisymm
    (finiteZ2NormalizedProductKernel_operator_norm_le_one hq0 hq1 n)
    (finiteZ2NormalizedProductKernel_operator_one_le_norm q n)

/-- Operator-norm normalization leaves the already stochastic product transfer
unchanged. -/
theorem finiteZ2NormalizedProductKernel_normalizedOperator_eq_operator
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (n : ℕ) :
    finiteKernelNormalizedOperator (finiteZ2NormalizedProductKernel q n) =
      finiteKernelOperator (finiteZ2NormalizedProductKernel q n) := by
  unfold finiteKernelNormalizedOperator
  rw [finiteZ2NormalizedProductKernel_operator_norm_eq_one hq0 hq1 n]
  simp

/-- Hilbert-space Rayleigh contraction of every zero-mass state by the same
local sign eigenvalue, independently of tensor dimension. -/
theorem finiteZ2NormalizedProductKernel_normalizedOperator_rayleigh_le
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (n : ℕ)
    (f : FiniteBoundaryHilbert (Fin n → Bool))
    (hmass : finiteFunctionMass f = 0) :
    inner ℝ
        (finiteKernelNormalizedOperator
          (finiteZ2NormalizedProductKernel q n) f) f ≤
      q * ‖f‖ ^ 2 := by
  rw [finiteZ2NormalizedProductKernel_normalizedOperator_eq_operator
    hq0 hq1]
  rw [← finiteFunctionKernelQuadratic_eq_inner_operator,
    ← finiteFunctionNormSq_eq_norm_sq]
  exact finiteZ2NormalizedProductKernel_quadratic_le_q_mul_of_mass_zero
    hq0 hq1 n f hmass

/-- Volume-independent Poincare/Dirichlet coercivity of the normalized Boolean
product transfer on the zero-mass sector. -/
theorem finiteZ2NormalizedProductKernel_normalizedOperator_poincare
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (n : ℕ)
    (f : FiniteBoundaryHilbert (Fin n → Bool))
    (hmass : finiteFunctionMass f = 0) :
    (1 - q) * ‖f‖ ^ 2 ≤
      inner ℝ
        (f - finiteKernelNormalizedOperator
          (finiteZ2NormalizedProductKernel q n) f) f := by
  have hrayleigh :=
    finiteZ2NormalizedProductKernel_normalizedOperator_rayleigh_le
      hq0 hq1 n f hmass
  rw [inner_sub_left, real_inner_self_eq_norm_sq]
  linarith

end

end MathlibAnalytic
end MGAP4D
