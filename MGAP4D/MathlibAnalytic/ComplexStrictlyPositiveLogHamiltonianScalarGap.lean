import MGAP4D.MathlibAnalytic.ComplexStrictlyPositiveLogHamiltonian
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped ComplexOrder

namespace ComplexStrictlyPositiveOperator

universe u

variable {H : Type u}
  [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]

/-- A positive scalar upper bound on a strictly positive transfer operator gives
its sharp logarithmic Hamiltonian lower bound.  This is the scalar-cap form of
the continuous-functional-calculus transport

`T ≤ q I  ⟹  -log(q) I ≤ -log(T)`.

Unlike finite-dimensional eigenvalue enumeration, this statement is directly
usable on compact/infinite-dimensional Hilbert carriers. -/
theorem neg_log_scalar_algebraMap_le_logHamiltonian_of_le_scalar
    [CompleteSpace H]
    (T : H →L[ℂ] H)
    (q : ℝ)
    (hq : 0 < q)
    (hstrict : IsStrictlyPositive T)
    (hle : T ≤ algebraMap ℝ (H →L[ℂ] H) q) :
    algebraMap ℝ (H →L[ℂ] H) (-Real.log q) ≤ logHamiltonian T := by
  refine
    algebraMap_le_logHamiltonian_of_le_exp_neg_algebraMap
      T (-Real.log q) hstrict ?_
  simpa [Real.exp_log hq] using hle

/-- The sharp half-transfer cap gives the support-energy lower bound `log 2`
without choosing an eigenbasis:

`T ≤ (1/2) I  ⟹  (log 2) I ≤ -log(T)`.

This is the functional-calculus endpoint needed downstream once the compact
geometric Wilson transfer is controlled by one half on its excited carrier. -/
theorem log_two_algebraMap_le_logHamiltonian_of_le_half
    [CompleteSpace H]
    (T : H →L[ℂ] H)
    (hstrict : IsStrictlyPositive T)
    (hle : T ≤ algebraMap ℝ (H →L[ℂ] H) (1 / 2 : ℝ)) :
    algebraMap ℝ (H →L[ℂ] H) (Real.log 2) ≤ logHamiltonian T := by
  have h :=
    neg_log_scalar_algebraMap_le_logHamiltonian_of_le_scalar
      T (1 / 2 : ℝ) (by norm_num) hstrict hle
  have hlog : -Real.log (1 / 2 : ℝ) = Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
    simp
  rw [hlog] at h
  exact h

end ComplexStrictlyPositiveOperator

end

end MathlibAnalytic
end MGAP4D
