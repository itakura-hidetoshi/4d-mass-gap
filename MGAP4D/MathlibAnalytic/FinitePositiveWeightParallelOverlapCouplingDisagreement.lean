import MGAP4D.MathlibAnalytic.FinitePositiveWeightParallelOverlapCoupling
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The coordinatewise expected Hamming disagreement carried by the canonical
parallel overlap coupling.  Because the parallel coupling is the product of
the one-site overlap couplings, this is the sum of the one-site disagreement
masses. -/
def finitePositiveWeightParallelOverlapExpectedHamming
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ configuration : ι → G, 0 < weight configuration)
    (leftEnvironment rightEnvironment : ι → G) : ℝ :=
  ∑ target : ι,
    (finitePositiveWeightSingleSiteOverlapCouplingData
      weight hweight leftEnvironment rightEnvironment target).disagreementMass

/-- The parallel expected Hamming disagreement is exactly one half of the sum
of the repository's unhalved one-site conditional `L¹` distances. -/
theorem finitePositiveWeightParallelOverlapExpectedHamming_eq_half_mul_sum_conditionalL1
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ configuration : ι → G, 0 < weight configuration)
    (leftEnvironment rightEnvironment : ι → G) :
    finitePositiveWeightParallelOverlapExpectedHamming
        weight hweight leftEnvironment rightEnvironment =
      (2 : ℝ)⁻¹ *
        ∑ target : ι,
          finitePositiveWeightSingleSiteConditionalL1
            weight leftEnvironment rightEnvironment target := by
  unfold finitePositiveWeightParallelOverlapExpectedHamming
  simp_rw [finitePositiveWeightSingleSiteOverlapCoupling_disagreementMass_eq_half_mul]
  rw [← Finset.mul_sum]

/-- Coefficient-friendly form: the expected Hamming disagreement is bounded by
the sum of the unhalved conditional `L¹` distances. -/
theorem finitePositiveWeightParallelOverlapExpectedHamming_le_sum_conditionalL1
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ configuration : ι → G, 0 < weight configuration)
    (leftEnvironment rightEnvironment : ι → G) :
    finitePositiveWeightParallelOverlapExpectedHamming
        weight hweight leftEnvironment rightEnvironment ≤
      ∑ target : ι,
        finitePositiveWeightSingleSiteConditionalL1
          weight leftEnvironment rightEnvironment target := by
  unfold finitePositiveWeightParallelOverlapExpectedHamming
  apply Finset.sum_le_sum
  intro target _hTarget
  exact finitePositiveWeightSingleSiteOverlapCoupling_disagreementMass_le
    weight hweight leftEnvironment rightEnvironment target

/-- If the two input environments differ only at one source coordinate, the
parallel overlap coupling's expected Hamming disagreement is bounded by the
corresponding influence column sum. -/
theorem finitePositiveWeightDobrushin_parallelOverlapExpectedHamming_le_columnSum
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ configuration : ι → G, 0 < weight configuration)
    (D : FinitePositiveWeightDobrushinL1MatrixData weight)
    (leftEnvironment rightEnvironment : ι → G)
    (source : ι)
    (hAgree : FiniteProductAgreeOff leftEnvironment rightEnvironment source) :
    finitePositiveWeightParallelOverlapExpectedHamming
        weight hweight leftEnvironment rightEnvironment ≤
      ∑ target : ι, D.influence target source := by
  unfold finitePositiveWeightParallelOverlapExpectedHamming
  apply Finset.sum_le_sum
  intro target _hTarget
  exact
    finitePositiveWeightDobrushin_singleSiteOverlapCoupling_disagreementMass_le
      weight hweight D leftEnvironment rightEnvironment target source hAgree

/-- A declared column coefficient immediately yields one-step parallel Hamming
contraction for inputs differing at one coordinate. -/
theorem finitePositiveWeightDobrushin_parallelOverlapExpectedHamming_lt_one
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ configuration : ι → G, 0 < weight configuration)
    (D : FinitePositiveWeightDobrushinL1MatrixData weight)
    (columnCoefficient : ℝ)
    (hColumn : ∀ source : ι,
      ∑ target : ι, D.influence target source ≤ columnCoefficient)
    (hColumnLtOne : columnCoefficient < 1)
    (leftEnvironment rightEnvironment : ι → G)
    (source : ι)
    (hAgree : FiniteProductAgreeOff leftEnvironment rightEnvironment source) :
    finitePositiveWeightParallelOverlapExpectedHamming
        weight hweight leftEnvironment rightEnvironment < 1 := by
  exact lt_of_le_of_lt
    (le_trans
      (finitePositiveWeightDobrushin_parallelOverlapExpectedHamming_le_columnSum
        weight hweight D leftEnvironment rightEnvironment source hAgree)
      (hColumn source))
    hColumnLtOne

end

end MathlibAnalytic
end MGAP4D
