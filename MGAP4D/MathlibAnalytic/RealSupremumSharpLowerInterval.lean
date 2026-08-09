import Mathlib.Data.Real.Basic
import Mathlib.Tactic

noncomputable section

open Set

namespace MGAP4D
namespace MathlibAnalytic

/-- A sharp supremum criterion for nonnegative real lower-bound sets.

If `s` is nonempty, every element of `s` is nonnegative and bounded above by
`M`, and every nonnegative real strictly below `M` belongs to `s`, then the
supremum of `s` is exactly `M`.

The proof does not require that `M` itself belong to `s`; density below the
endpoint suffices.  This is the order-theoretic form needed for variational
recovery arguments where the limiting optimum need not be attained at finite
scale. -/
theorem real_csSup_eq_of_nonempty_nonneg_upper_of_all_lt_mem
    (s : Set ℝ)
    (M : ℝ)
    (hNonempty : s.Nonempty)
    (hNonneg : ∀ x ∈ s, 0 ≤ x)
    (hUpper : ∀ x ∈ s, x ≤ M)
    (hBelow : ∀ x : ℝ, 0 ≤ x → x < M → x ∈ s) :
    sSup s = M := by
  have hBdd : BddAbove s := ⟨M, hUpper⟩
  have hSup_le : sSup s ≤ M :=
    csSup_le hNonempty hUpper
  have hSup_nonneg : 0 ≤ sSup s := by
    rcases hNonempty with ⟨x, hx⟩
    exact (hNonneg x hx).trans (le_csSup hBdd hx)
  have hM_le : M ≤ sSup s := by
    by_contra hnot
    have hSup_lt_M : sSup s < M := lt_of_not_ge hnot
    let y : ℝ := (sSup s + M) / 2
    have hy_nonneg : 0 ≤ y := by
      dsimp [y]
      linarith
    have hSup_lt_y : sSup s < y := by
      dsimp [y]
      linarith
    have hy_lt_M : y < M := by
      dsimp [y]
      linarith
    have hy_mem : y ∈ s := hBelow y hy_nonneg hy_lt_M
    have hy_le_Sup : y ≤ sSup s := le_csSup hBdd hy_mem
    linarith
  exact le_antisymm hSup_le hM_le

end MathlibAnalytic
end MGAP4D

end