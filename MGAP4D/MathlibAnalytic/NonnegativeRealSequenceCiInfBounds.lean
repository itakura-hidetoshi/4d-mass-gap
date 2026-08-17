import MGAP4D.MathlibAnalytic.NonnegativeAntitoneRealSequenceLimit

/-!
# Bounds for conditional infima of nonnegative real sequences

If every term of a real sequence is nonnegative, then its conditional infimum
is nonnegative and lies below every term.  This is a direct use of
`isGLB_ciInf` with zero as an explicit lower bound.
-/

namespace MGAP4D

open Set

/-- The conditional infimum of a nonnegative real sequence is itself
nonnegative and is bounded above by every sequence term. -/
theorem nonnegativeRealSequence_ciInf_bounds
    (f : ℕ → ℝ)
    (hnonneg : ∀ n : ℕ, 0 ≤ f n) :
    0 ≤ (⨅ n : ℕ, f n) ∧ ∀ n : ℕ, (⨅ k : ℕ, f k) ≤ f n := by
  have hbdd : BddBelow (range f) := by
    refine ⟨0, ?_⟩
    rintro y ⟨n, rfl⟩
    exact hnonneg n
  have hglb : IsGLB (range f) (⨅ n : ℕ, f n) := isGLB_ciInf hbdd
  constructor
  · exact hglb.2 (by
      intro y hy
      rcases hy with ⟨n, rfl⟩
      exact hnonneg n)
  · intro n
    exact hglb.1 ⟨n, rfl⟩

end MGAP4D
