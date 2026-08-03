import MGAP4D.MathlibAnalytic.FiniteZ2TensorProductUniformPoincare
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

/-- Exact two-point quadratic decomposition into trivial and sign modes. -/
theorem finiteZ2NormalizedLocalKernel_quadratic_split
    (q u0 u1 v0 v1 : ℝ) :
    (∑ a : Bool, ∑ b : Bool,
      (if a = false then u0 else u1) *
        finiteZ2NormalizedLocalKernel q a b *
        (if b = false then v0 else v1)) =
      2 * (((u0 + u1) / 2) * ((v0 + v1) / 2) +
        q * ((u0 - u1) / 2) * ((v0 - v1) / 2)) := by
  norm_num [finiteZ2NormalizedLocalKernel]
  ring

/-- The Boolean-cube product quadratic form splits into the even head sector
and the odd head sector, with the latter multiplied by the local sign
eigenvalue `q`. -/
theorem finiteFunctionKernelQuadratic_succ
    (q : ℝ) {n : ℕ}
    (f : (Fin (n + 1) → Bool) → ℝ) :
    finiteFunctionKernelQuadratic
        (finiteZ2NormalizedProductKernel q (n + 1)) f =
      2 * (finiteFunctionKernelQuadratic
          (finiteZ2NormalizedProductKernel q n)
          (finiteZ2HeadAverage f) +
        q * finiteFunctionKernelQuadratic
          (finiteZ2NormalizedProductKernel q n)
          (finiteZ2HeadDifference f)) := by
  rw [finiteFunctionKernelQuadratic_equiv
    (finSuccFunctionEquiv Bool n)
    (finiteZ2NormalizedProductKernel q (n + 1)) f]
  unfold finiteFunctionKernelQuadratic
  simp_rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  calc
    (∑ A : Fin n → Bool,
        ∑ a : Bool,
          ∑ b : Bool,
            ∑ B : Fin n → Bool,
              f ((finSuccFunctionEquiv Bool n).symm (a, A)) *
                  finiteZ2NormalizedProductKernel q (n + 1)
                    ((finSuccFunctionEquiv Bool n).symm (a, A))
                    ((finSuccFunctionEquiv Bool n).symm (b, B)) *
                f ((finSuccFunctionEquiv Bool n).symm (b, B))) =
      ∑ A : Fin n → Bool,
        ∑ B : Fin n → Bool,
          ∑ a : Bool,
            ∑ b : Bool,
              f ((finSuccFunctionEquiv Bool n).symm (a, A)) *
                  finiteZ2NormalizedProductKernel q (n + 1)
                    ((finSuccFunctionEquiv Bool n).symm (a, A))
                    ((finSuccFunctionEquiv Bool n).symm (b, B)) *
                f ((finSuccFunctionEquiv Bool n).symm (b, B)) := by
      apply Finset.sum_congr rfl
      intro A _hA
      calc
        (∑ a : Bool, ∑ b : Bool, ∑ B : Fin n → Bool, _) =
            ∑ a : Bool, ∑ B : Fin n → Bool, ∑ b : Bool, _ := by
          apply Finset.sum_congr rfl
          intro a _ha
          rw [Finset.sum_comm]
        _ = ∑ B : Fin n → Bool, ∑ a : Bool, ∑ b : Bool, _ := by
          rw [Finset.sum_comm]
    _ = ∑ A : Fin n → Bool,
        ∑ B : Fin n → Bool,
          2 * (finiteZ2HeadAverage f A * finiteZ2HeadAverage f B +
              q * finiteZ2HeadDifference f A * finiteZ2HeadDifference f B) *
            finiteZ2NormalizedProductKernel q n A B := by
      apply Finset.sum_congr rfl
      intro A _hA
      apply Finset.sum_congr rfl
      intro B _hB
      have hsplit := finiteZ2NormalizedLocalKernel_quadratic_split
        q
        (finiteZ2HeadFalse f A) (finiteZ2HeadTrue f A)
        (finiteZ2HeadFalse f B) (finiteZ2HeadTrue f B)
      calc
        (∑ a : Bool, ∑ b : Bool,
            f ((finSuccFunctionEquiv Bool n).symm (a, A)) *
                finiteZ2NormalizedProductKernel q (n + 1)
                  ((finSuccFunctionEquiv Bool n).symm (a, A))
                  ((finSuccFunctionEquiv Bool n).symm (b, B)) *
              f ((finSuccFunctionEquiv Bool n).symm (b, B))) =
          finiteZ2NormalizedProductKernel q n A B *
            (∑ a : Bool, ∑ b : Bool,
              (if a = false then finiteZ2HeadFalse f A
                else finiteZ2HeadTrue f A) *
                finiteZ2NormalizedLocalKernel q a b *
                (if b = false then finiteZ2HeadFalse f B
                  else finiteZ2HeadTrue f B)) := by
            apply Finset.sum_congr rfl
            intro a _ha
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b _hb
            cases a <;> cases b <;>
              simp [finSuccFunctionEquiv,
                finiteZ2HeadFalse, finiteZ2HeadTrue,
                finiteZ2NormalizedProductKernel_succ_apply] <;>
              ring
        _ = finiteZ2NormalizedProductKernel q n A B *
            (2 * (((finiteZ2HeadFalse f A + finiteZ2HeadTrue f A) / 2) *
                ((finiteZ2HeadFalse f B + finiteZ2HeadTrue f B) / 2) +
              q * ((finiteZ2HeadFalse f A - finiteZ2HeadTrue f A) / 2) *
                ((finiteZ2HeadFalse f B - finiteZ2HeadTrue f B) / 2))) := by
            rw [hsplit]
        _ = 2 * (finiteZ2HeadAverage f A * finiteZ2HeadAverage f B +
              q * finiteZ2HeadDifference f A * finiteZ2HeadDifference f B) *
            finiteZ2NormalizedProductKernel q n A B := by
            simp [finiteZ2HeadAverage, finiteZ2HeadDifference]
            ring
    _ = 2 * (finiteFunctionKernelQuadratic
          (finiteZ2NormalizedProductKernel q n)
          (finiteZ2HeadAverage f) +
        q * finiteFunctionKernelQuadratic
          (finiteZ2NormalizedProductKernel q n)
          (finiteZ2HeadDifference f)) := by
      simp only [finiteFunctionKernelQuadratic]
      simp_rw [mul_add, Finset.sum_add_distrib]
      rw [mul_add, Finset.mul_sum, Finset.mul_sum]
      congr 1 <;>
        rw [Finset.mul_sum] <;>
        apply Finset.sum_congr rfl <;>
        intro A _hA <;>
        rw [Finset.mul_sum] <;>
        apply Finset.sum_congr rfl <;>
        intro B _hB <;>
        ring

/-- Squared finite-function norms are nonnegative. -/
theorem finiteFunctionNormSq_nonneg
    {α : Type} [Fintype α]
    (f : α → ℝ) :
    0 ≤ finiteFunctionNormSq f := by
  exact Finset.sum_nonneg fun x _hx => sq_nonneg (f x)

/-- The normalized Boolean product kernel has a nonnegative quadratic form and
is bounded above by the Euclidean squared norm, uniformly in the cube
dimension. -/
theorem finiteZ2NormalizedProductKernel_quadratic_mem_normInterval
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (n : ℕ)
    (f : (Fin n → Bool) → ℝ) :
    0 ≤ finiteFunctionKernelQuadratic
        (finiteZ2NormalizedProductKernel q n) f ∧
      finiteFunctionKernelQuadratic
          (finiteZ2NormalizedProductKernel q n) f ≤
        finiteFunctionNormSq f := by
  induction n with
  | zero =>
      simp [finiteFunctionKernelQuadratic, finiteFunctionNormSq,
        finiteZ2NormalizedProductKernel, finiteTensorKernelMatrix]
  | succ n ih =>
      rw [finiteFunctionKernelQuadratic_succ,
        finiteFunctionNormSq_succ]
      have ha := ih (finiteZ2HeadAverage f)
      have hd := ih (finiteZ2HeadDifference f)
      have hnd := finiteFunctionNormSq_nonneg (finiteZ2HeadDifference f)
      constructor
      · have hqhd :
          0 ≤ q * finiteFunctionKernelQuadratic
            (finiteZ2NormalizedProductKernel q n)
            (finiteZ2HeadDifference f) :=
          mul_nonneg hq0 hd.1
        linarith
      · have hq_le :
          q * finiteFunctionKernelQuadratic
              (finiteZ2NormalizedProductKernel q n)
              (finiteZ2HeadDifference f) ≤
            finiteFunctionNormSq (finiteZ2HeadDifference f) := by
          calc
            q * finiteFunctionKernelQuadratic
                (finiteZ2NormalizedProductKernel q n)
                (finiteZ2HeadDifference f) ≤
              q * finiteFunctionNormSq (finiteZ2HeadDifference f) :=
                mul_le_mul_of_nonneg_left hd.2 hq0
            _ ≤ finiteFunctionNormSq (finiteZ2HeadDifference f) := by
              nlinarith
        linarith

/-- A zero-mass Boolean-cube function contracts in Rayleigh quotient by the
single-coordinate sign eigenvalue `q`, independently of the number of
coordinates. -/
theorem finiteZ2NormalizedProductKernel_quadratic_le_q_mul_of_mass_zero
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (n : ℕ)
    (f : (Fin n → Bool) → ℝ)
    (hmass : finiteFunctionMass f = 0) :
    finiteFunctionKernelQuadratic
        (finiteZ2NormalizedProductKernel q n) f ≤
      q * finiteFunctionNormSq f := by
  induction n with
  | zero =>
      have hf : f = 0 := by
        funext A
        have hA : A = (fun i : Fin 0 => Fin.elim0 i) := Subsingleton.elim _ _
        subst A
        simpa [finiteFunctionMass] using hmass
      subst f
      simp [finiteFunctionKernelQuadratic, finiteFunctionNormSq]
  | succ n ih =>
      rw [finiteFunctionKernelQuadratic_succ,
        finiteFunctionNormSq_succ]
      have hmassAverage :
          finiteFunctionMass (finiteZ2HeadAverage f) = 0 := by
        rw [finiteFunctionMass_succ] at hmass
        linarith
      have ha := ih (finiteZ2HeadAverage f) hmassAverage
      have hd :=
        finiteZ2NormalizedProductKernel_quadratic_mem_normInterval
          hq0 hq1 n (finiteZ2HeadDifference f)
      have hqhd :
          q * finiteFunctionKernelQuadratic
              (finiteZ2NormalizedProductKernel q n)
              (finiteZ2HeadDifference f) ≤
            q * finiteFunctionNormSq (finiteZ2HeadDifference f) :=
        mul_le_mul_of_nonneg_left hd.2 hq0
      nlinarith

end

end MathlibAnalytic
end MGAP4D
