import MGAP4D.MathlibAnalytic.FiniteTensorProductKernelPosDef
import MGAP4D.MathlibAnalytic.FiniteOSGramKernelEuclideanTransfer
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

/-- Symmetric normalized two-point kernel with trivial eigenvalue `1` and
sign eigenvalue `q`. -/
def finiteZ2NormalizedLocalKernel
    (q : ℝ) (x y : Bool) : ℝ :=
  if x = y then (1 + q) / 2 else (1 - q) / 2

@[simp] theorem finiteZ2NormalizedLocalKernel_false_false
    (q : ℝ) :
    finiteZ2NormalizedLocalKernel q false false = (1 + q) / 2 := by
  simp [finiteZ2NormalizedLocalKernel]

@[simp] theorem finiteZ2NormalizedLocalKernel_true_true
    (q : ℝ) :
    finiteZ2NormalizedLocalKernel q true true = (1 + q) / 2 := by
  simp [finiteZ2NormalizedLocalKernel]

@[simp] theorem finiteZ2NormalizedLocalKernel_false_true
    (q : ℝ) :
    finiteZ2NormalizedLocalKernel q false true = (1 - q) / 2 := by
  simp [finiteZ2NormalizedLocalKernel]

@[simp] theorem finiteZ2NormalizedLocalKernel_true_false
    (q : ℝ) :
    finiteZ2NormalizedLocalKernel q true false = (1 - q) / 2 := by
  simp [finiteZ2NormalizedLocalKernel]

/-- The normalized local kernel is symmetric. -/
theorem finiteZ2NormalizedLocalKernel_symmetric
    (q : ℝ) (x y : Bool) :
    finiteZ2NormalizedLocalKernel q x y =
      finiteZ2NormalizedLocalKernel q y x := by
  by_cases h : x = y
  · subst y
    rfl
  · have hyx : y ≠ x := Ne.symm h
    simp [finiteZ2NormalizedLocalKernel, h, hyx]

/-- Every row of the local normalized kernel has mass one. -/
theorem finiteZ2NormalizedLocalKernel_row_sum
    (q : ℝ) (y : Bool) :
    ∑ x : Bool, finiteZ2NormalizedLocalKernel q x y = 1 := by
  cases y <;>
    norm_num [finiteZ2NormalizedLocalKernel] <;>
    ring

/-- The local normalized kernel is entrywise nonnegative for `q ∈ [-1,1]`. -/
theorem finiteZ2NormalizedLocalKernel_nonneg
    {q : ℝ} (hqLower : -1 ≤ q) (hqUpper : q ≤ 1)
    (x y : Bool) :
    0 ≤ finiteZ2NormalizedLocalKernel q x y := by
  by_cases h : x = y
  · simp [finiteZ2NormalizedLocalKernel, h]
    linarith
  · simp [finiteZ2NormalizedLocalKernel, h]
    linarith

/-- Simultaneous-update product kernel on the finite Boolean cube. -/
def finiteZ2NormalizedProductKernel
    (q : ℝ) (n : ℕ) :
    (Fin n → Bool) → (Fin n → Bool) → ℝ :=
  finiteTensorKernelMatrix
    (fun x y : Bool => finiteZ2NormalizedLocalKernel q x y) n

/-- Pointwise product formula for the Boolean-cube kernel. -/
theorem finiteZ2NormalizedProductKernel_apply
    (q : ℝ) (n : ℕ)
    (A B : Fin n → Bool) :
    finiteZ2NormalizedProductKernel q n A B =
      ∏ i : Fin n, finiteZ2NormalizedLocalKernel q (A i) (B i) := by
  exact finiteTensorKernelMatrix_apply
    (fun x y : Bool => finiteZ2NormalizedLocalKernel q x y) n A B

/-- Head-tail recursion for the Boolean-cube product kernel. -/
theorem finiteZ2NormalizedProductKernel_succ_apply
    (q : ℝ) (n : ℕ)
    (a b : Bool)
    (A B : Fin n → Bool) :
    finiteZ2NormalizedProductKernel q (n + 1)
        (Fin.cases a A) (Fin.cases b B) =
      finiteZ2NormalizedLocalKernel q a b *
        finiteZ2NormalizedProductKernel q n A B := by
  rw [finiteZ2NormalizedProductKernel_apply,
    Fin.prod_univ_succ,
    finiteZ2NormalizedProductKernel_apply]
  rfl

/-- Total mass of a real function on a finite carrier. -/
def finiteFunctionMass
    {α : Type} [Fintype α]
    (f : α → ℝ) : ℝ :=
  ∑ x : α, f x

/-- Squared Euclidean norm written as a finite sum. -/
def finiteFunctionNormSq
    {α : Type} [Fintype α]
    (f : α → ℝ) : ℝ :=
  ∑ x : α, (f x) ^ 2

/-- Quadratic form of a finite scalar kernel on ordinary real functions. -/
def finiteFunctionKernelQuadratic
    {α : Type} [Fintype α]
    (kernel : α → α → ℝ)
    (f : α → ℝ) : ℝ :=
  ∑ x : α, ∑ y : α, f x * kernel x y * f y

/-- Finite total mass is invariant under reindexing by an equivalence. -/
theorem finiteFunctionMass_equiv
    {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : α → ℝ) :
    finiteFunctionMass f =
      finiteFunctionMass (fun y : β => f (e.symm y)) := by
  unfold finiteFunctionMass
  refine Fintype.sum_equiv e _ _ ?_
  intro x
  simp

/-- Finite squared norm is invariant under reindexing by an equivalence. -/
theorem finiteFunctionNormSq_equiv
    {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : α → ℝ) :
    finiteFunctionNormSq f =
      finiteFunctionNormSq (fun y : β => f (e.symm y)) := by
  unfold finiteFunctionNormSq
  refine Fintype.sum_equiv e _ _ ?_
  intro x
  simp

/-- Finite kernel quadratic forms are invariant under simultaneous
reindexing of the carrier. -/
theorem finiteFunctionKernelQuadratic_equiv
    {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β)
    (kernel : α → α → ℝ)
    (f : α → ℝ) :
    finiteFunctionKernelQuadratic kernel f =
      finiteFunctionKernelQuadratic
        (fun x y : β => kernel (e.symm x) (e.symm y))
        (fun x : β => f (e.symm x)) := by
  unfold finiteFunctionKernelQuadratic
  refine Fintype.sum_equiv e _ _ ?_
  intro x
  refine Fintype.sum_equiv e _ _ ?_
  intro y
  simp

/-- False-head restriction of a Boolean-cube function. -/
def finiteZ2HeadFalse
    {n : ℕ}
    (f : (Fin (n + 1) → Bool) → ℝ) :
    (Fin n → Bool) → ℝ :=
  fun A => f (Fin.cases false A)

/-- True-head restriction of a Boolean-cube function. -/
def finiteZ2HeadTrue
    {n : ℕ}
    (f : (Fin (n + 1) → Bool) → ℝ) :
    (Fin n → Bool) → ℝ :=
  fun A => f (Fin.cases true A)

/-- Even component in the first Boolean coordinate. -/
def finiteZ2HeadAverage
    {n : ℕ}
    (f : (Fin (n + 1) → Bool) → ℝ) :
    (Fin n → Bool) → ℝ :=
  fun A => (finiteZ2HeadFalse f A + finiteZ2HeadTrue f A) / 2

/-- Odd component in the first Boolean coordinate. -/
def finiteZ2HeadDifference
    {n : ℕ}
    (f : (Fin (n + 1) → Bool) → ℝ) :
    (Fin n → Bool) → ℝ :=
  fun A => (finiteZ2HeadFalse f A - finiteZ2HeadTrue f A) / 2

/-- Reconstruction of the false-head restriction from its even and odd parts. -/
theorem finiteZ2HeadFalse_eq_average_add_difference
    {n : ℕ}
    (f : (Fin (n + 1) → Bool) → ℝ)
    (A : Fin n → Bool) :
    finiteZ2HeadFalse f A =
      finiteZ2HeadAverage f A + finiteZ2HeadDifference f A := by
  simp [finiteZ2HeadFalse, finiteZ2HeadTrue,
    finiteZ2HeadAverage, finiteZ2HeadDifference]
  ring

/-- Reconstruction of the true-head restriction from its even and odd parts. -/
theorem finiteZ2HeadTrue_eq_average_sub_difference
    {n : ℕ}
    (f : (Fin (n + 1) → Bool) → ℝ)
    (A : Fin n → Bool) :
    finiteZ2HeadTrue f A =
      finiteZ2HeadAverage f A - finiteZ2HeadDifference f A := by
  simp [finiteZ2HeadFalse, finiteZ2HeadTrue,
    finiteZ2HeadAverage, finiteZ2HeadDifference]
  ring

/-- Total mass of a cube function is twice the mass of its even head part. -/
theorem finiteFunctionMass_succ
    {n : ℕ}
    (f : (Fin (n + 1) → Bool) → ℝ) :
    finiteFunctionMass f =
      2 * finiteFunctionMass (finiteZ2HeadAverage f) := by
  rw [finiteFunctionMass_equiv (finSuccFunctionEquiv Bool n) f]
  unfold finiteFunctionMass
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  calc
    (∑ A : Fin n → Bool,
        ∑ a : Bool,
          f ((finSuccFunctionEquiv Bool n).symm (a, A))) =
      ∑ A : Fin n → Bool,
        (finiteZ2HeadFalse f A + finiteZ2HeadTrue f A) := by
      apply Finset.sum_congr rfl
      intro A _hA
      simp [finSuccFunctionEquiv, finiteZ2HeadFalse, finiteZ2HeadTrue, add_comm]
    _ = 2 * ∑ A : Fin n → Bool, finiteZ2HeadAverage f A := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A _hA
      simp [finiteZ2HeadAverage]
      ring

/-- Pythagorean head decomposition of the squared Euclidean norm. -/
theorem finiteFunctionNormSq_succ
    {n : ℕ}
    (f : (Fin (n + 1) → Bool) → ℝ) :
    finiteFunctionNormSq f =
      2 * (finiteFunctionNormSq (finiteZ2HeadAverage f) +
        finiteFunctionNormSq (finiteZ2HeadDifference f)) := by
  rw [finiteFunctionNormSq_equiv (finSuccFunctionEquiv Bool n) f]
  unfold finiteFunctionNormSq
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  calc
    (∑ A : Fin n → Bool,
        ∑ a : Bool,
          (f ((finSuccFunctionEquiv Bool n).symm (a, A))) ^ 2) =
      ∑ A : Fin n → Bool,
        ((finiteZ2HeadFalse f A) ^ 2 +
          (finiteZ2HeadTrue f A) ^ 2) := by
      apply Finset.sum_congr rfl
      intro A _hA
      simp [finSuccFunctionEquiv, finiteZ2HeadFalse, finiteZ2HeadTrue, add_comm]
    _ = 2 *
        ((∑ A : Fin n → Bool, (finiteZ2HeadAverage f A) ^ 2) +
          ∑ A : Fin n → Bool, (finiteZ2HeadDifference f A) ^ 2) := by
      rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro A _hA
      simp [finiteZ2HeadAverage, finiteZ2HeadDifference]
      ring

end

end MathlibAnalytic
end MGAP4D
