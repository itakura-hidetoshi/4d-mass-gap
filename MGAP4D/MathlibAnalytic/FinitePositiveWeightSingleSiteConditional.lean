import MGAP4D.MathlibAnalytic.FiniteZ2GaugeProductKernelLikelihoodRatio
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Partition function obtained by freezing every coordinate except one and
summing a strictly positive real weight over the finite one-site carrier. -/
def finitePositiveWeightSingleSitePartition
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (A : ι → G)
    (e : ι) : ℝ :=
  ∑ g : G, weight (Function.update A e g)

/-- A pointwise-positive weight has a strictly positive one-site partition
function whenever the one-site carrier is nonempty. -/
theorem finitePositiveWeightSingleSitePartition_pos
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (A : ι → G)
    (e : ι) :
    0 < finitePositiveWeightSingleSitePartition weight A e := by
  classical
  let g₀ : G := Classical.choice (inferInstance : Nonempty G)
  unfold finitePositiveWeightSingleSitePartition
  exact Finset.sum_pos
    (fun g _hg => hweight (Function.update A e g))
    ⟨g₀, Finset.mem_univ g₀⟩

/-- Real conditional probability obtained by normalizing a positive finite
weight on one coordinate fiber. -/
def finitePositiveWeightSingleSiteProbability
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (A : ι → G)
    (e : ι)
    (g : G) : ℝ :=
  weight (Function.update A e g) /
    finitePositiveWeightSingleSitePartition weight A e

/-- Every one-site conditional probability is strictly positive. -/
theorem finitePositiveWeightSingleSiteProbability_pos
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (A : ι → G)
    (e : ι)
    (g : G) :
    0 < finitePositiveWeightSingleSiteProbability weight A e g := by
  unfold finitePositiveWeightSingleSiteProbability
  exact div_pos
    (hweight (Function.update A e g))
    (finitePositiveWeightSingleSitePartition_pos weight hweight A e)

/-- The real one-site conditional probabilities have total mass one. -/
theorem finitePositiveWeightSingleSiteProbability_sum_eq_one
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (A : ι → G)
    (e : ι) :
    ∑ g : G, finitePositiveWeightSingleSiteProbability weight A e g = 1 := by
  classical
  unfold finitePositiveWeightSingleSiteProbability
  rw [← Finset.sum_div]
  change
    finitePositiveWeightSingleSitePartition weight A e /
        finitePositiveWeightSingleSitePartition weight A e = 1
  exact div_self
    (ne_of_gt
      (finitePositiveWeightSingleSitePartition_pos weight hweight A e))

/-- A common likelihood-ratio bound on the unnormalized fiber weights survives
normalization by their common one-site partition function. -/
theorem finitePositiveWeightSingleSiteProbability_le_ratio_mul
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (A : ι → G)
    (e : ι)
    (ratio : ℝ)
    (hRatio : ∀ g h : G,
      weight (Function.update A e g) ≤
        ratio * weight (Function.update A e h))
    (g h : G) :
    finitePositiveWeightSingleSiteProbability weight A e g ≤
      ratio * finitePositiveWeightSingleSiteProbability weight A e h := by
  unfold finitePositiveWeightSingleSiteProbability
  have hZ :
      0 < finitePositiveWeightSingleSitePartition weight A e :=
    finitePositiveWeightSingleSitePartition_pos weight hweight A e
  calc
    weight (Function.update A e g) /
          finitePositiveWeightSingleSitePartition weight A e ≤
        (ratio * weight (Function.update A e h)) /
          finitePositiveWeightSingleSitePartition weight A e :=
      (div_le_div_iff_of_pos_right hZ).2 (hRatio g h)
    _ = ratio *
        (weight (Function.update A e h) /
          finitePositiveWeightSingleSitePartition weight A e) := by
      ring

/-- Conditional expectation along one coordinate fiber for a positive finite
weight. -/
def finitePositiveWeightSingleSiteExpectation
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (f : (ι → G) → ℝ)
    (A : ι → G)
    (e : ι) : ℝ :=
  ∑ g : G,
    finitePositiveWeightSingleSiteProbability weight A e g *
      f (Function.update A e g)

/-- Conditional variance along one coordinate fiber. -/
def finitePositiveWeightSingleSiteVariance
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (f : (ι → G) → ℝ)
    (A : ι → G)
    (e : ι) : ℝ :=
  ∑ g : G,
    finitePositiveWeightSingleSiteProbability weight A e g *
      (f (Function.update A e g) -
        finitePositiveWeightSingleSiteExpectation weight f A e) ^ 2

/-- Every positive-weight one-site conditional variance is nonnegative. -/
theorem finitePositiveWeightSingleSiteVariance_nonneg
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (f : (ι → G) → ℝ)
    (A : ι → G)
    (e : ι) :
    0 ≤ finitePositiveWeightSingleSiteVariance weight f A e := by
  classical
  unfold finitePositiveWeightSingleSiteVariance
  apply Finset.sum_nonneg
  intro g _hg
  exact mul_nonneg
    (le_of_lt
      (finitePositiveWeightSingleSiteProbability_pos
        weight hweight A e g))
    (sq_nonneg _)

/-- Pairwise local Dirichlet form associated with one positive-weight
conditional distribution. -/
def finitePositiveWeightSingleSitePairDirichlet
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (f : (ι → G) → ℝ)
    (A : ι → G)
    (e : ι) : ℝ :=
  (2 : ℝ)⁻¹ *
    ∑ g : G, ∑ h : G,
      finitePositiveWeightSingleSiteProbability weight A e g *
        finitePositiveWeightSingleSiteProbability weight A e h *
          (f (Function.update A e g) -
            f (Function.update A e h)) ^ 2

/-- The local pair Dirichlet form is nonnegative. -/
theorem finitePositiveWeightSingleSitePairDirichlet_nonneg
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (f : (ι → G) → ℝ)
    (A : ι → G)
    (e : ι) :
    0 ≤ finitePositiveWeightSingleSitePairDirichlet weight f A e := by
  unfold finitePositiveWeightSingleSitePairDirichlet
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro g _hg
  apply Finset.sum_nonneg
  intro h _hh
  exact mul_nonneg
    (mul_nonneg
      (le_of_lt
        (finitePositiveWeightSingleSiteProbability_pos
          weight hweight A e g))
      (le_of_lt
        (finitePositiveWeightSingleSiteProbability_pos
          weight hweight A e h)))
    (sq_nonneg _)

end

end MathlibAnalytic
end MGAP4D
