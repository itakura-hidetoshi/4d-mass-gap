import MGAP4D.MathlibAnalytic.FiniteNonnegativeInfluenceKernelMaximumColumn
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The finite set of row sums of a nonnegative influence kernel. -/
noncomputable def finiteInfluenceKernelRowSumValues
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι) : Finset ℝ := by
  classical
  exact Finset.univ.image (finiteInfluenceKernelRowSum K)

/-- The exact maximum row sum of a finite nonnegative influence kernel. -/
noncomputable def finiteInfluenceKernelMaximumRowSum
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Nonempty ι]
    (K : FiniteNonnegativeInfluenceKernelData ι) : ℝ :=
  (finiteInfluenceKernelRowSumValues K).max' (by
    classical
    let target : ι := Classical.choice (inferInstance : Nonempty ι)
    refine ⟨finiteInfluenceKernelRowSum K target, ?_⟩
    exact Finset.mem_image.mpr
      ⟨target, Finset.mem_univ target, rfl⟩)

/-- Every concrete row is bounded by the exact maximum row sum. -/
theorem finiteInfluenceKernelRowSum_le_maximum
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Nonempty ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (target : ι) :
    finiteInfluenceKernelRowSum K target ≤
      finiteInfluenceKernelMaximumRowSum K := by
  classical
  unfold finiteInfluenceKernelMaximumRowSum
  apply Finset.le_max'
  exact Finset.mem_image.mpr
    ⟨target, Finset.mem_univ target, rfl⟩

/-- The exact maximum row sum is nonnegative. -/
theorem finiteInfluenceKernelMaximumRowSum_nonneg
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Nonempty ι]
    (K : FiniteNonnegativeInfluenceKernelData ι) :
    0 ≤ finiteInfluenceKernelMaximumRowSum K := by
  let target : ι := Classical.choice (inferInstance : Nonempty ι)
  exact
    (Finset.sum_nonneg fun source _ =>
      K.influence_nonneg target source).trans
      (finiteInfluenceKernelRowSum_le_maximum K target)

/-- A strict maximum row sum is equivalent to a uniform strict row bound. -/
theorem finiteInfluenceKernelMaximumRowSum_lt_one_iff
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Nonempty ι]
    (K : FiniteNonnegativeInfluenceKernelData ι) :
    finiteInfluenceKernelMaximumRowSum K < 1 ↔
      ∃ coefficient : ℝ,
        0 ≤ coefficient ∧ coefficient < 1 ∧
          ∀ target : ι,
            finiteInfluenceKernelRowSum K target ≤ coefficient := by
  constructor
  · intro h
    exact ⟨finiteInfluenceKernelMaximumRowSum K,
      finiteInfluenceKernelMaximumRowSum_nonneg K, h,
      finiteInfluenceKernelRowSum_le_maximum K⟩
  · rintro ⟨coefficient, _hNonneg, hLt, hRows⟩
    classical
    unfold finiteInfluenceKernelMaximumRowSum
    rw [Finset.max'_lt_iff]
    intro value hValue
    rcases Finset.mem_image.mp hValue with ⟨target, _hTarget, rfl⟩
    exact lt_of_le_of_lt (hRows target) hLt

/-- A pointwise row bound controls the exact maximum row sum. -/
theorem finiteInfluenceKernelMaximumRowSum_le_of_forall
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Nonempty ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (bound : ℝ)
    (hRows : ∀ target : ι,
      finiteInfluenceKernelRowSum K target ≤ bound) :
    finiteInfluenceKernelMaximumRowSum K ≤ bound := by
  classical
  unfold finiteInfluenceKernelMaximumRowSum
  rw [Finset.max'_le_iff]
  intro value hValue
  rcases Finset.mem_image.mp hValue with ⟨target, _hTarget, rfl⟩
  exact hRows target

/-- A pointwise column bound controls the exact maximum column sum. -/
theorem finiteInfluenceKernelMaximumColumnSum_le_of_forall
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Nonempty ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (bound : ℝ)
    (hColumns : ∀ source : ι,
      finiteInfluenceKernelColumnSum K source ≤ bound) :
    finiteInfluenceKernelMaximumColumnSum K ≤ bound := by
  classical
  unfold finiteInfluenceKernelMaximumColumnSum
  rw [Finset.max'_le_iff]
  intro value hValue
  rcases Finset.mem_image.mp hValue with ⟨source, _hSource, rfl⟩
  exact hColumns source

end

end MathlibAnalytic
end MGAP4D
