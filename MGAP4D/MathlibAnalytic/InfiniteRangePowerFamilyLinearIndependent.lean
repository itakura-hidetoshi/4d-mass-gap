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
    simpa [pa, pb] using hx
  have hpEq : pa = pb := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine hf.mono ?_
    intro y hy
    rcases hy with ⟨x, rfl⟩
    exact hpEval x
  have hcoeff := congrArg (fun q : Polynomial ℝ => q.coeff i) hpEq
  simpa [pa, pb, hi] using hcoeff

end

end MathlibAnalytic
end MGAP4D
