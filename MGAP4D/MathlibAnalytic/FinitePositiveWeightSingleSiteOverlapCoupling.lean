import MGAP4D.MathlibAnalytic.FiniteRealProbabilityOverlapCouplingDisagreement
import MGAP4D.MathlibAnalytic.FinitePositiveWeightDobrushinInfluence
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A one-site conditional law of a strictly positive finite product weight,
packaged as a finite real probability law. -/
noncomputable def finitePositiveWeightSingleSiteProbabilityData
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ configuration : ι → G, 0 < weight configuration)
    (environment : ι → G)
    (target : ι) :
    FiniteRealProbabilityData G :=
  { probability :=
      finitePositiveWeightSingleSiteProbability weight environment target
    probability_nonneg := fun g =>
      le_of_lt
        (finitePositiveWeightSingleSiteProbability_pos
          weight hweight environment target g)
    probability_sum_eq_one :=
      finitePositiveWeightSingleSiteProbability_sum_eq_one
        weight hweight environment target }

/-- The canonical correct-marginal overlap coupling between two one-site
conditional laws at the same target coordinate. -/
noncomputable def finitePositiveWeightSingleSiteOverlapCouplingData
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ configuration : ι → G, 0 < weight configuration)
    (leftEnvironment rightEnvironment : ι → G)
    (target : ι) :
    FiniteRealCouplingData
      (finitePositiveWeightSingleSiteProbabilityData
        weight hweight leftEnvironment target)
      (finitePositiveWeightSingleSiteProbabilityData
        weight hweight rightEnvironment target) :=
  (finitePositiveWeightSingleSiteProbabilityData
      weight hweight leftEnvironment target).overlapCouplingData
    (finitePositiveWeightSingleSiteProbabilityData
      weight hweight rightEnvironment target)

/-- The left marginal is exactly the original left one-site conditional law. -/
theorem finitePositiveWeightSingleSiteOverlapCoupling_leftMarginal
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ configuration : ι → G, 0 < weight configuration)
    (leftEnvironment rightEnvironment : ι → G)
    (target : ι)
    (g : G) :
    ∑ h : G,
      (finitePositiveWeightSingleSiteOverlapCouplingData
        weight hweight leftEnvironment rightEnvironment target).joint g h =
      finitePositiveWeightSingleSiteProbability
        weight leftEnvironment target g := by
  simpa [finitePositiveWeightSingleSiteOverlapCouplingData,
    finitePositiveWeightSingleSiteProbabilityData] using
    (finitePositiveWeightSingleSiteOverlapCouplingData
      weight hweight leftEnvironment rightEnvironment target).left_marginal g

/-- The right marginal is exactly the original right one-site conditional law. -/
theorem finitePositiveWeightSingleSiteOverlapCoupling_rightMarginal
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ configuration : ι → G, 0 < weight configuration)
    (leftEnvironment rightEnvironment : ι → G)
    (target : ι)
    (h : G) :
    ∑ g : G,
      (finitePositiveWeightSingleSiteOverlapCouplingData
        weight hweight leftEnvironment rightEnvironment target).joint g h =
      finitePositiveWeightSingleSiteProbability
        weight rightEnvironment target h := by
  simpa [finitePositiveWeightSingleSiteOverlapCouplingData,
    finitePositiveWeightSingleSiteProbabilityData] using
    (finitePositiveWeightSingleSiteOverlapCouplingData
      weight hweight leftEnvironment rightEnvironment target).right_marginal h

/-- The `L¹` distance of the packaged one-site laws is definitionally the
repository's conditional `L¹` distance. -/
theorem finitePositiveWeightSingleSiteProbabilityData_l1Distance
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ configuration : ι → G, 0 < weight configuration)
    (leftEnvironment rightEnvironment : ι → G)
    (target : ι) :
    (finitePositiveWeightSingleSiteProbabilityData
        weight hweight leftEnvironment target).l1Distance
      (finitePositiveWeightSingleSiteProbabilityData
        weight hweight rightEnvironment target) =
      finitePositiveWeightSingleSiteConditionalL1
        weight leftEnvironment rightEnvironment target := by
  rfl

/-- The one-site overlap coupling disagrees with probability exactly one half
of the unhalved conditional `L¹` distance. -/
theorem finitePositiveWeightSingleSiteOverlapCoupling_disagreementMass_eq_half_mul
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ configuration : ι → G, 0 < weight configuration)
    (leftEnvironment rightEnvironment : ι → G)
    (target : ι) :
    (finitePositiveWeightSingleSiteOverlapCouplingData
        weight hweight leftEnvironment rightEnvironment target).disagreementMass =
      (2 : ℝ)⁻¹ *
        finitePositiveWeightSingleSiteConditionalL1
          weight leftEnvironment rightEnvironment target := by
  let P := finitePositiveWeightSingleSiteProbabilityData
    weight hweight leftEnvironment target
  let Q := finitePositiveWeightSingleSiteProbabilityData
    weight hweight rightEnvironment target
  have hDisagreement :=
    P.overlapCouplingData_disagreementMass_eq_half_mul_l1Distance Q
  simpa [finitePositiveWeightSingleSiteOverlapCouplingData,
    finitePositiveWeightSingleSiteProbabilityData_l1Distance,
    P, Q] using hDisagreement

/-- Coefficient-friendly form: one-site coupling disagreement is bounded by
conditional `L¹`. -/
theorem finitePositiveWeightSingleSiteOverlapCoupling_disagreementMass_le
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ configuration : ι → G, 0 < weight configuration)
    (leftEnvironment rightEnvironment : ι → G)
    (target : ι) :
    (finitePositiveWeightSingleSiteOverlapCouplingData
        weight hweight leftEnvironment rightEnvironment target).disagreementMass ≤
      finitePositiveWeightSingleSiteConditionalL1
        weight leftEnvironment rightEnvironment target := by
  rw [finitePositiveWeightSingleSiteOverlapCoupling_disagreementMass_eq_half_mul]
  have hL1 := finitePositiveWeightSingleSiteConditionalL1_nonneg
    weight leftEnvironment rightEnvironment target
  nlinarith

/-- If two environments differ only at one source coordinate, the canonical
one-site overlap coupling disagrees with probability bounded by the declared
Dobrushin influence entry. -/
theorem finitePositiveWeightDobrushin_singleSiteOverlapCoupling_disagreementMass_le
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
    (target source : ι)
    (hAgree : FiniteProductAgreeOff leftEnvironment rightEnvironment source) :
    (finitePositiveWeightSingleSiteOverlapCouplingData
        weight hweight leftEnvironment rightEnvironment target).disagreementMass ≤
      D.influence target source := by
  exact le_trans
    (finitePositiveWeightSingleSiteOverlapCoupling_disagreementMass_le
      weight hweight leftEnvironment rightEnvironment target)
    (D.conditionalL1_le target source
      leftEnvironment rightEnvironment hAgree)

end

end MathlibAnalytic
end MGAP4D
