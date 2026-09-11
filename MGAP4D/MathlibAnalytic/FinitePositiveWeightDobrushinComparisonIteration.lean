import MGAP4D.MathlibAnalytic.FiniteNonnegativeKernelComparisonIteration
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The generic nonnegative-kernel comparison iteration specialized to the
influence matrix carried by finite positive-weight Dobrushin data. -/
theorem finitePositiveWeightDobrushinComparison_iterate
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    {weight : (ι → G) → ℝ}
    (D : FinitePositiveWeightDobrushinL1MatrixData weight)
    (b d : ι → ℝ)
    (hComparison :
      ∀ target : ι,
        d target ≤ b target +
          finiteNonnegativeKernelApply D.influence d target)
    (n : ℕ)
    (target : ι) :
    d target ≤
      finiteNonnegativeKernelPartialResolvent D.influence b n target +
        finiteNonnegativeKernelPowerApply D.influence d n target := by
  exact
    finiteNonnegativeKernelComparison_iterate
      D.influence D.influence_nonneg b d hComparison n target

/-- Under the Dobrushin row coefficient, the residual in the finite comparison
iteration is bounded by the corresponding geometric term. -/
theorem finitePositiveWeightDobrushinComparison_iterate_le_partial_add_geometricResidual
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    {weight : (ι → G) → ℝ}
    (D : FinitePositiveWeightDobrushinL1MatrixData weight)
    (b d : ι → ℝ)
    (distanceBound : ℝ)
    (hDistanceBound : 0 ≤ distanceBound)
    (hd : ∀ target : ι, d target ≤ distanceBound)
    (hComparison :
      ∀ target : ι,
        d target ≤ b target +
          finiteNonnegativeKernelApply D.influence d target)
    (n : ℕ)
    (target : ι) :
    d target ≤
      finiteNonnegativeKernelPartialResolvent D.influence b n target +
        D.coefficient ^ n * distanceBound := by
  exact
    finiteNonnegativeKernelComparison_iterate_le_partial_add_geometricResidual
      D.influence D.influence_nonneg
      D.coefficient D.coefficient_nonneg D.rowSum_le_coefficient
      b d distanceBound hDistanceBound hd hComparison n target

/-- The Dobrushin coefficient lies in the half-open unit interval. -/
theorem finitePositiveWeightDobrushin_coefficient_mem_Ico
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    {weight : (ι → G) → ℝ}
    (D : FinitePositiveWeightDobrushinL1MatrixData weight) :
    D.coefficient ∈ Set.Ico (0 : ℝ) 1 := by
  exact ⟨D.coefficient_nonneg, D.coefficient_lt_one⟩

/-- A nonnegative source vector gives nonnegative finite Dobrushin partial
resolvents. -/
theorem finitePositiveWeightDobrushin_partialResolvent_nonneg
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    {weight : (ι → G) → ℝ}
    (D : FinitePositiveWeightDobrushinL1MatrixData weight)
    (b : ι → ℝ)
    (hb : ∀ target : ι, 0 ≤ b target)
    (n : ℕ)
    (target : ι) :
    0 ≤ finiteNonnegativeKernelPartialResolvent D.influence b n target := by
  exact
    finiteNonnegativeKernelPartialResolvent_nonneg
      D.influence D.influence_nonneg b hb n target

end

end MathlibAnalytic
end MGAP4D
