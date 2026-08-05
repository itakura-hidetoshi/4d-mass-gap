import MGAP4D.MathlibAnalytic.FinitePositiveWeightConditionalScaleZeroInfluence
import Mathlib.Topology.Order.Lattice
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A pointwise continuous finite weight family has continuous one-site
partition functions. -/
theorem continuous_finitePositiveWeightSingleSitePartition
    {X ι G : Type}
    [TopologicalSpace X]
    [DecidableEq ι]
    [Fintype G]
    (weight : X → (ι → G) → ℝ)
    (hweight : ∀ configuration : ι → G,
      Continuous (fun x => weight x configuration))
    (A : ι → G)
    (e : ι) :
    Continuous (fun x =>
      finitePositiveWeightSingleSitePartition (weight x) A e) := by
  classical
  unfold finitePositiveWeightSingleSitePartition
  apply continuous_finset_sum
  intro g _hg
  exact hweight (Function.update A e g)

/-- Strict positivity makes normalization continuous: every one-site
conditional probability varies continuously with a pointwise continuous
positive finite weight family. -/
theorem continuous_finitePositiveWeightSingleSiteProbability
    {X ι G : Type}
    [TopologicalSpace X]
    [DecidableEq ι]
    [Fintype G]
    [Nonempty G]
    (weight : X → (ι → G) → ℝ)
    (hweight : ∀ configuration : ι → G,
      Continuous (fun x => weight x configuration))
    (hweightPos : ∀ x configuration, 0 < weight x configuration)
    (A : ι → G)
    (e : ι)
    (g : G) :
    Continuous (fun x =>
      finitePositiveWeightSingleSiteProbability (weight x) A e g) := by
  unfold finitePositiveWeightSingleSiteProbability
  exact (hweight (Function.update A e g)).div
    (continuous_finitePositiveWeightSingleSitePartition
      weight hweight A e)
    (fun x => ne_of_gt
      (finitePositiveWeightSingleSitePartition_pos
        (weight x) (hweightPos x) A e))

/-- Conditional total variation in the repository's unhalved `L¹`
normalization is continuous for pointwise continuous positive finite weights. -/
theorem continuous_finitePositiveWeightSingleSiteConditionalL1
    {X ι G : Type}
    [TopologicalSpace X]
    [DecidableEq ι]
    [Fintype G]
    [Nonempty G]
    (weight : X → (ι → G) → ℝ)
    (hweight : ∀ configuration : ι → G,
      Continuous (fun x => weight x configuration))
    (hweightPos : ∀ x configuration, 0 < weight x configuration)
    (A B : ι → G)
    (target : ι) :
    Continuous (fun x =>
      finitePositiveWeightSingleSiteConditionalL1
        (weight x) A B target) := by
  classical
  unfold finitePositiveWeightSingleSiteConditionalL1
  apply continuous_finset_sum
  intro g _hg
  exact ((continuous_finitePositiveWeightSingleSiteProbability
      weight hweight hweightPos A target g).sub
    (continuous_finitePositiveWeightSingleSiteProbability
      weight hweight hweightPos B target g)).abs

/-- Each finite source-replacement candidate appearing before the canonical
maximum is a continuous scalar function of a pointwise continuous positive
weight family. -/
theorem continuous_finitePositiveWeightConditionalL1SourceCandidate
    {X ι G : Type}
    [TopologicalSpace X]
    [DecidableEq ι]
    [Fintype G]
    [Nonempty G]
    (weight : X → (ι → G) → ℝ)
    (hweight : ∀ configuration : ι → G,
      Continuous (fun x => weight x configuration))
    (hweightPos : ∀ x configuration, 0 < weight x configuration)
    (target source : ι)
    (pair : (ι → G) × (ι → G)) :
    Continuous (fun x =>
      if FiniteProductAgreeOff pair.1 pair.2 source then
        finitePositiveWeightSingleSiteConditionalL1
          (weight x) pair.1 pair.2 target
      else 0) := by
  classical
  by_cases hAgree : FiniteProductAgreeOff pair.1 pair.2 source
  · simpa [hAgree] using
      continuous_finitePositiveWeightSingleSiteConditionalL1
        weight hweight hweightPos pair.1 pair.2 target
  · simpa [hAgree] using (continuous_const : Continuous (fun _x : X => (0 : ℝ)))

end

end MathlibAnalytic
end MGAP4D
