import MGAP4D.MathlibAnalytic.FinitePositiveWeightParallelOverlapCoupling
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Coordinatewise disagreement profile of the canonical parallel product
coupling. -/
def finitePositiveWeightParallelDisagreementProfile
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ configuration : ι → G, 0 < weight configuration)
    (leftEnvironment rightEnvironment : ι → G)
    (target : ι) : ℝ :=
  (finitePositiveWeightSingleSiteOverlapCouplingData
    weight hweight leftEnvironment rightEnvironment target).disagreementMass

/-- Total coordinate-disagreement mass of the canonical parallel product
coupling.  The later full Hamming-expectation theorem identifies this finite
sum with the expectation under the product joint law. -/
def finitePositiveWeightParallelTotalCoordinateDisagreement
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
    finitePositiveWeightParallelDisagreementProfile
      weight hweight leftEnvironment rightEnvironment target

/-- Each coordinate profile is exactly half the repository's unhalved
conditional `L¹` distance. -/
theorem finitePositiveWeightParallelDisagreementProfile_eq_half_mul
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ configuration : ι → G, 0 < weight configuration)
    (leftEnvironment rightEnvironment : ι → G)
    (target : ι) :
    finitePositiveWeightParallelDisagreementProfile
        weight hweight leftEnvironment rightEnvironment target =
      (2 : ℝ)⁻¹ *
        finitePositiveWeightSingleSiteConditionalL1
          weight leftEnvironment rightEnvironment target := by
  exact
    finitePositiveWeightSingleSiteOverlapCoupling_disagreementMass_eq_half_mul
      weight hweight leftEnvironment rightEnvironment target

/-- The total coordinate-disagreement mass is half the sum of all target
conditional `L¹` distances. -/
theorem finitePositiveWeightParallelTotalCoordinateDisagreement_eq_half_sum
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ configuration : ι → G, 0 < weight configuration)
    (leftEnvironment rightEnvironment : ι → G) :
    finitePositiveWeightParallelTotalCoordinateDisagreement
        weight hweight leftEnvironment rightEnvironment =
      (2 : ℝ)⁻¹ *
        ∑ target : ι,
          finitePositiveWeightSingleSiteConditionalL1
            weight leftEnvironment rightEnvironment target := by
  unfold finitePositiveWeightParallelTotalCoordinateDisagreement
  simp_rw [finitePositiveWeightParallelDisagreementProfile_eq_half_mul]
  rw [Finset.mul_sum]

/-- A coefficient-friendly upper bound by the unhalved conditional `L¹`
sum. -/
theorem finitePositiveWeightParallelTotalCoordinateDisagreement_le_sum
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ configuration : ι → G, 0 < weight configuration)
    (leftEnvironment rightEnvironment : ι → G) :
    finitePositiveWeightParallelTotalCoordinateDisagreement
        weight hweight leftEnvironment rightEnvironment ≤
      ∑ target : ι,
        finitePositiveWeightSingleSiteConditionalL1
          weight leftEnvironment rightEnvironment target := by
  rw [finitePositiveWeightParallelTotalCoordinateDisagreement_eq_half_sum]
  have hSum :
      0 ≤ ∑ target : ι,
        finitePositiveWeightSingleSiteConditionalL1
          weight leftEnvironment rightEnvironment target :=
    Finset.sum_nonneg fun target _hTarget =>
      finitePositiveWeightSingleSiteConditionalL1_nonneg
        weight leftEnvironment rightEnvironment target
  nlinarith

/-- For a pair of environments differing only at one source, every target
coordinate disagreement is bounded by the declared influence entry. -/
theorem finitePositiveWeightDobrushin_parallelDisagreementProfile_le
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
    (source target : ι)
    (hAgree : FiniteProductAgreeOff
      leftEnvironment rightEnvironment source) :
    finitePositiveWeightParallelDisagreementProfile
        weight hweight leftEnvironment rightEnvironment target ≤
      D.influence target source := by
  exact
    finitePositiveWeightDobrushin_singleSiteOverlapCoupling_disagreementMass_le
      weight hweight D leftEnvironment rightEnvironment target source hAgree

/-- A single-source input discrepancy produces total parallel coordinate
 disagreement bounded by the corresponding influence column. -/
theorem finitePositiveWeightDobrushin_parallelTotalCoordinateDisagreement_le_columnSum
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
    (hAgree : FiniteProductAgreeOff
      leftEnvironment rightEnvironment source) :
    finitePositiveWeightParallelTotalCoordinateDisagreement
        weight hweight leftEnvironment rightEnvironment ≤
      ∑ target : ι, D.influence target source := by
  unfold finitePositiveWeightParallelTotalCoordinateDisagreement
  exact Finset.sum_le_sum fun target _hTarget =>
    finitePositiveWeightDobrushin_parallelDisagreementProfile_le
      weight hweight D leftEnvironment rightEnvironment
      source target hAgree

end

end MathlibAnalytic
end MGAP4D
