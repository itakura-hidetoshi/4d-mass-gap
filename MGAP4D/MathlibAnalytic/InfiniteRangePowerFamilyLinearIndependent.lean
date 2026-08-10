import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic

namespace MGAP4D
namespace MathlibAnalytic

open Function Set

noncomputable section

/-- A real-valued function with infinite range has linearly independent power
functions `x ↦ f x ^ n`.

The proof converts a finite linear relation into one real polynomial.  The
relation forces that polynomial to vanish on the infinite range of `f`, so
`Polynomial.eq_zero_of_infinite_isRoot` makes the polynomial identically zero;
coefficient comparison then kills every coefficient of the original relation.
-/
theorem infiniteRange_powerFamily_linearIndependent
    {X : Type*}
    (f : X → ℝ)
    (hf : (Set.range f).Infinite) :
    LinearIndependent ℝ (fun n : ℕ => fun x : X => f x ^ n) := by
  rw [linearIndependent_iff'ₛ]
  intro s a b hab i hi
  let p : ℝ[X] :=
    ∑ j ∈ s, Polynomial.monomial j (a j - b j)
  have hpEval : ∀ x : X, p.eval (f x) = 0 := by
    intro x
    have hx := congrFun hab x
    have hx' :
        (∑ j ∈ s, a j * f x ^ j) =
          ∑ j ∈ s, b j * f x ^ j := by
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hx
    calc
      p.eval (f x) = ∑ j ∈ s, (a j - b j) * f x ^ j := by
        simp [p]
      _ = (∑ j ∈ s, a j * f x ^ j) -
          ∑ j ∈ s, b j * f x ^ j := by
        simp_rw [sub_mul]
        exact Finset.sum_sub_distrib
      _ = 0 := sub_eq_zero.mpr hx'
  have hpZero : p = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot p
    refine hf.mono ?_
    intro y hy
    rcases hy with ⟨x, rfl⟩
    simpa only [Polynomial.IsRoot] using hpEval x
  have hcoeff := congrArg (fun q : ℝ[X] => q.coeff i) hpZero
  have hab_i : a i - b i = 0 := by
    simpa [p, hi] using hcoeff
  exact sub_eq_zero.mp hab_i

end

end MathlibAnalytic
end MGAP4D
