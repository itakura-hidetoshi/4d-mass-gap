import MGAP4D.MathlibAnalytic.FinitePositiveWeightReciprocalInfluenceKernelResponse
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The finite set of column sums of a nonnegative influence kernel. -/
noncomputable def finiteInfluenceKernelColumnSumValues
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι) : Finset ℝ := by
  classical
  exact Finset.univ.image (finiteInfluenceKernelColumnSum K)

/-- The exact maximum column sum of a finite nonnegative influence kernel. -/
noncomputable def finiteInfluenceKernelMaximumColumnSum
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Nonempty ι]
    (K : FiniteNonnegativeInfluenceKernelData ι) : ℝ :=
  (finiteInfluenceKernelColumnSumValues K).max' (by
    classical
    let source : ι := Classical.choice (inferInstance : Nonempty ι)
    refine ⟨finiteInfluenceKernelColumnSum K source, ?_⟩
    exact Finset.mem_image.mpr
      ⟨source, Finset.mem_univ source, rfl⟩)

/-- Every concrete column is bounded by the exact maximum column sum. -/
theorem finiteInfluenceKernelColumnSum_le_maximum
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Nonempty ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (source : ι) :
    finiteInfluenceKernelColumnSum K source ≤
      finiteInfluenceKernelMaximumColumnSum K := by
  classical
  unfold finiteInfluenceKernelMaximumColumnSum
  apply Finset.le_max'
  exact Finset.mem_image.mpr
    ⟨source, Finset.mem_univ source, rfl⟩

/-- The exact maximum column sum is nonnegative. -/
theorem finiteInfluenceKernelMaximumColumnSum_nonneg
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Nonempty ι]
    (K : FiniteNonnegativeInfluenceKernelData ι) :
    0 ≤ finiteInfluenceKernelMaximumColumnSum K := by
  let source : ι := Classical.choice (inferInstance : Nonempty ι)
  exact
    (Finset.sum_nonneg fun target _ =>
      K.influence_nonneg target source).trans
      (finiteInfluenceKernelColumnSum_le_maximum K source)

/-- A strict maximum column sum supplies exactly the column fields of the
reciprocal response certificate. -/
theorem finiteInfluenceKernelMaximumColumnSum_lt_one_iff
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Nonempty ι]
    (K : FiniteNonnegativeInfluenceKernelData ι) :
    finiteInfluenceKernelMaximumColumnSum K < 1 ↔
      ∃ coefficient : ℝ,
        0 ≤ coefficient ∧ coefficient < 1 ∧
          ∀ source : ι,
            finiteInfluenceKernelColumnSum K source ≤ coefficient := by
  constructor
  · intro h
    exact ⟨finiteInfluenceKernelMaximumColumnSum K,
      finiteInfluenceKernelMaximumColumnSum_nonneg K, h,
      finiteInfluenceKernelColumnSum_le_maximum K⟩
  · rintro ⟨coefficient, _hNonneg, hLt, hColumns⟩
    classical
    unfold finiteInfluenceKernelMaximumColumnSum
    rw [Finset.max'_lt_iff]
    intro value hValue
    rcases Finset.mem_image.mp hValue with ⟨source, _hSource, rfl⟩
    exact lt_of_le_of_lt (hColumns source) hLt

end

end MathlibAnalytic
end MGAP4D
