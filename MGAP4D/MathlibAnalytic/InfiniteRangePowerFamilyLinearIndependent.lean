import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic

namespace MGAP4D
namespace MathlibAnalytic

open Function Set

noncomputable section

/-- A real-valued function with infinite range has linearly independent power
functions `x ↦ f x ^ n`.

The proof converts a finite linear relation into two real polynomials.  Their
evaluations agree on the infinite range of `f`, so
`Polynomial.eq_of_infinite_eval_eq` makes the polynomials equal; coefficient
comparison then recovers equality of every coefficient in the original finite
relation. -/
theorem infiniteRange_powerFamily_linearIndependent
    {α : Type*}
    (f : α → ℝ)
    (hf : (Set.range f).Infinite) :
    LinearIndependent ℝ (fun n : ℕ => fun x : α => f x ^ n) := by
  rw [linearIndependent_iff'ₛ]
  intro s a b hab i hi
  let pa : Polynomial ℝ :=
    ∑ j ∈ s, Polynomial.monomial j (a j)
  let pb : Polynomial ℝ :=
    ∑ j ∈ s, Polynomial.monomial j (b j)
  have hpEval : ∀ x : α, pa.eval (f x) = pb.eval (f x) := by
    intro x
    have hx := congrFun hab x
    have hx' :
        (∑ j ∈ s, a j * f x ^ j) =
          ∑ j ∈ s, b j * f x ^ j := by
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hx
    have hpa : pa.eval (f x) = ∑ j ∈ s, a j * f x ^ j := by
      change (∑ j ∈ s, Polynomial.monomial j (a j)).eval (f x) =
        ∑ j ∈ s, a j * f x ^ j
      rw [Polynomial.eval_finset_sum]
      simp
    have hpb : pb.eval (f x) = ∑ j ∈ s, b j * f x ^ j := by
      change (∑ j ∈ s, Polynomial.monomial j (b j)).eval (f x) =
        ∑ j ∈ s, b j * f x ^ j
      rw [Polynomial.eval_finset_sum]
      simp
    exact hpa.trans (hx'.trans hpb.symm)
  have hpEq : pa = pb := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine hf.mono ?_
    intro y hy
    rcases hy with ⟨x, rfl⟩
    exact hpEval x
  have hca : pa.coeff i = a i := by
    change (∑ j ∈ s, Polynomial.monomial j (a j)).coeff i = a i
    rw [Polynomial.finset_sum_coeff]
    calc
      (∑ j ∈ s, (Polynomial.monomial j (a j)).coeff i) =
          (Polynomial.monomial i (a i)).coeff i := by
        apply Finset.sum_eq_single i
        · intro j hj hji
          exact Polynomial.coeff_monomial_of_ne (a j) hji.symm
        · intro hnot
          exact (hnot hi).elim
      _ = a i := Polynomial.coeff_monomial_same i (a i)
  have hcb : pb.coeff i = b i := by
    change (∑ j ∈ s, Polynomial.monomial j (b j)).coeff i = b i
    rw [Polynomial.finset_sum_coeff]
    calc
      (∑ j ∈ s, (Polynomial.monomial j (b j)).coeff i) =
          (Polynomial.monomial i (b i)).coeff i := by
        apply Finset.sum_eq_single i
        · intro j hj hji
          exact Polynomial.coeff_monomial_of_ne (b j) hji.symm
        · intro hnot
          exact (hnot hi).elim
      _ = b i := Polynomial.coeff_monomial_same i (b i)
  calc
    a i = pa.coeff i := hca.symm
    _ = pb.coeff i := congrArg (fun q : Polynomial ℝ => q.coeff i) hpEq
    _ = b i := hcb

end

end MathlibAnalytic
end MGAP4D
