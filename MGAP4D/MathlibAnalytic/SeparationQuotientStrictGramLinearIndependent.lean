import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.SeparationQuotient
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

universe u

/-- A family in a seminormed real vector space whose every nonzero finitely
supported linear combination has strictly positive seminorm descends to a
linearly independent family in the separation quotient.

This is the exact abstract mechanism needed for OS reconstruction: strict
positivity excludes every nontrivial finite linear combination from the null
space identified by `SeparationQuotient`. -/
theorem separationQuotient_linearIndependent_of_linearCombination_norm_pos
    {V : Type u} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    (v : ℕ → V)
    (hPos : ∀ l : ℕ →₀ ℝ, l ≠ 0 →
      0 < ‖Finsupp.linearCombination ℝ v l‖) :
    LinearIndependent ℝ (fun n => SeparationQuotient.mk (v n)) := by
  rw [linearIndependent_iff_injective_finsuppLinearCombination]
  intro l₁ l₂ hEq
  by_contra hne
  have hDiff : l₁ - l₂ ≠ 0 := sub_ne_zero.mpr hne
  have hQuotientZero :
      Finsupp.linearCombination ℝ
          (fun n => SeparationQuotient.mk (v n)) (l₁ - l₂) = 0 := by
    rw [map_sub, hEq, sub_self]
  have hMk :
      SeparationQuotient.mk
          (Finsupp.linearCombination ℝ v (l₁ - l₂)) = 0 := by
    simpa [Finsupp.linearCombination_apply] using hQuotientZero
  have hNormZero :
      ‖Finsupp.linearCombination ℝ v (l₁ - l₂)‖ = 0 := by
    have hqNorm :
        ‖SeparationQuotient.mk
            (Finsupp.linearCombination ℝ v (l₁ - l₂))‖ = 0 := by
      rw [hMk, norm_zero]
    simpa using hqNorm
  have hStrict := hPos (l₁ - l₂) hDiff
  rw [hNormZero] at hStrict
  exact (lt_irrefl 0) hStrict

/-- The same criterion in inner-product form.  Strict positivity of the Gram
quadratic form for every nonzero finitely supported coefficient vector implies
linear independence after separation. -/
theorem separationQuotient_linearIndependent_of_linearCombination_inner_pos
    {V : Type u} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]
    (v : ℕ → V)
    (hPos : ∀ l : ℕ →₀ ℝ, l ≠ 0 →
      0 < inner ℝ
        (Finsupp.linearCombination ℝ v l)
        (Finsupp.linearCombination ℝ v l)) :
    LinearIndependent ℝ (fun n => SeparationQuotient.mk (v n)) := by
  apply separationQuotient_linearIndependent_of_linearCombination_norm_pos v
  intro l hl
  have hSq : 0 < ‖Finsupp.linearCombination ℝ v l‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    exact hPos l hl
  nlinarith [norm_nonneg (Finsupp.linearCombination ℝ v l)]

end

end MathlibAnalytic
end MGAP4D
