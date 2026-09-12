import MGAP4D.MathlibAnalytic.FiniteKernelGroundStateDoobPosteriorProbability
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A pointwise positive finite weight has positive total mass. -/
theorem finiteRealWeightPartition_pos_of_pos
    {α : Type}
    [Fintype α]
    [Nonempty α]
    (weight : α → ℝ)
    (hweight : ∀ x : α, 0 < weight x) :
    0 < finiteRealWeightPartition weight := by
  classical
  let x0 : α := Classical.choice inferInstance
  unfold finiteRealWeightPartition
  exact Finset.sum_pos
    (fun x _hx => hweight x)
    ⟨x0, Finset.mem_univ x0⟩

/-- Raw finite mixture of component weights with positive external scales. -/
def finitePositiveWeightMixtureRaw
    {ι α : Type}
    [Fintype ι]
    (scale : ι → ℝ)
    (weight : ι → α → ℝ)
    (x : α) : ℝ :=
  ∑ i : ι, scale i * weight i x

/-- Every raw mixture value is positive when all scales and component weights
are positive. -/
theorem finitePositiveWeightMixtureRaw_pos
    {ι α : Type}
    [Fintype ι]
    [Nonempty ι]
    (scale : ι → ℝ)
    (weight : ι → α → ℝ)
    (hscale : ∀ i : ι, 0 < scale i)
    (hweight : ∀ i : ι, ∀ x : α, 0 < weight i x)
    (x : α) :
    0 < finitePositiveWeightMixtureRaw scale weight x := by
  classical
  let i0 : ι := Classical.choice inferInstance
  unfold finitePositiveWeightMixtureRaw
  exact Finset.sum_pos
    (fun i _hi => mul_pos (hscale i) (hweight i x))
    ⟨i0, Finset.mem_univ i0⟩

/-- Partition of one mixture component. -/
def finitePositiveWeightMixtureComponentPartition
    {ι α : Type}
    [Fintype α]
    (weight : ι → α → ℝ)
    (i : ι) : ℝ :=
  finiteRealWeightPartition (weight i)

/-- The effective mixture-index weight is the external scale times the
component partition. -/
def finitePositiveWeightMixtureIndexWeight
    {ι α : Type}
    [Fintype α]
    (scale : ι → ℝ)
    (weight : ι → α → ℝ)
    (i : ι) : ℝ :=
  scale i * finitePositiveWeightMixtureComponentPartition weight i

/-- Total effective index weight. -/
def finitePositiveWeightMixtureIndexPartition
    {ι α : Type}
    [Fintype ι]
    [Fintype α]
    (scale : ι → ℝ)
    (weight : ι → α → ℝ) : ℝ :=
  ∑ i : ι, finitePositiveWeightMixtureIndexWeight scale weight i

/-- The raw mixture partition is exactly the total effective index weight. -/
theorem finitePositiveWeightMixtureRaw_partition
    {ι α : Type}
    [Fintype ι]
    [Fintype α]
    (scale : ι → ℝ)
    (weight : ι → α → ℝ) :
    finiteRealWeightPartition
        (finitePositiveWeightMixtureRaw scale weight) =
      finitePositiveWeightMixtureIndexPartition scale weight := by
  unfold finiteRealWeightPartition finitePositiveWeightMixtureRaw
    finitePositiveWeightMixtureIndexPartition
    finitePositiveWeightMixtureIndexWeight
    finitePositiveWeightMixtureComponentPartition
  calc
    (∑ x : α, ∑ i : ι, scale i * weight i x) =
        ∑ i : ι, ∑ x : α, scale i * weight i x := by
      rw [Finset.sum_comm]
    _ = ∑ i : ι, scale i * ∑ x : α, weight i x := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]

/-- Every component partition is positive. -/
theorem finitePositiveWeightMixtureComponentPartition_pos
    {ι α : Type}
    [Fintype α]
    [Nonempty α]
    (weight : ι → α → ℝ)
    (hweight : ∀ i : ι, ∀ x : α, 0 < weight i x)
    (i : ι) :
    0 < finitePositiveWeightMixtureComponentPartition weight i := by
  exact finiteRealWeightPartition_pos_of_pos (weight i) (hweight i)

/-- Every effective mixture-index weight is positive. -/
theorem finitePositiveWeightMixtureIndexWeight_pos
    {ι α : Type}
    [Fintype α]
    [Nonempty α]
    (scale : ι → ℝ)
    (weight : ι → α → ℝ)
    (hscale : ∀ i : ι, 0 < scale i)
    (hweight : ∀ i : ι, ∀ x : α, 0 < weight i x)
    (i : ι) :
    0 < finitePositiveWeightMixtureIndexWeight scale weight i := by
  exact mul_pos (hscale i)
    (finitePositiveWeightMixtureComponentPartition_pos weight hweight i)

/-- The total effective index weight is positive. -/
theorem finitePositiveWeightMixtureIndexPartition_pos
    {ι α : Type}
    [Fintype ι]
    [Nonempty ι]
    [Fintype α]
    [Nonempty α]
    (scale : ι → ℝ)
    (weight : ι → α → ℝ)
    (hscale : ∀ i : ι, 0 < scale i)
    (hweight : ∀ i : ι, ∀ x : α, 0 < weight i x) :
    0 < finitePositiveWeightMixtureIndexPartition scale weight := by
  exact finiteRealWeightPartition_pos_of_pos
    (finitePositiveWeightMixtureIndexWeight scale weight)
    (finitePositiveWeightMixtureIndexWeight_pos scale weight hscale hweight)

/-- Normalized probability law of one mixture component. -/
noncomputable def finitePositiveWeightMixtureComponentProbabilityData
    {ι α : Type}
    [Fintype α]
    [Nonempty α]
    (weight : ι → α → ℝ)
    (hweight : ∀ i : ι, ∀ x : α, 0 < weight i x)
    (i : ι) :
    FiniteRealProbabilityData α :=
  finiteRealWeightProbabilityData
    (weight i)
    (fun x => le_of_lt (hweight i x))
    (finitePositiveWeightMixtureComponentPartition_pos weight hweight i)

/-- Probability law of the latent mixture index. -/
noncomputable def finitePositiveWeightMixtureIndexProbabilityData
    {ι α : Type}
    [Fintype ι]
    [Nonempty ι]
    [Fintype α]
    [Nonempty α]
    (scale : ι → ℝ)
    (weight : ι → α → ℝ)
    (hscale : ∀ i : ι, 0 < scale i)
    (hweight : ∀ i : ι, ∀ x : α, 0 < weight i x) :
    FiniteRealProbabilityData ι :=
  finiteRealWeightProbabilityData
    (finitePositiveWeightMixtureIndexWeight scale weight)
    (fun i => le_of_lt
      (finitePositiveWeightMixtureIndexWeight_pos
        scale weight hscale hweight i))
    (finitePositiveWeightMixtureIndexPartition_pos
      scale weight hscale hweight)

/-- Normalized probability law of the raw mixture weight. -/
noncomputable def finitePositiveWeightMixtureProbabilityData
    {ι α : Type}
    [Fintype ι]
    [Nonempty ι]
    [Fintype α]
    [Nonempty α]
    (scale : ι → ℝ)
    (weight : ι → α → ℝ)
    (hscale : ∀ i : ι, 0 < scale i)
    (hweight : ∀ i : ι, ∀ x : α, 0 < weight i x) :
    FiniteRealProbabilityData α :=
  finiteRealWeightProbabilityData
    (finitePositiveWeightMixtureRaw scale weight)
    (fun x => le_of_lt
      (finitePositiveWeightMixtureRaw_pos scale weight hscale hweight x))
    (by
      rw [finitePositiveWeightMixtureRaw_partition]
      exact finitePositiveWeightMixtureIndexPartition_pos
        scale weight hscale hweight)

/-- The normalized raw mixture is exactly the convex mixture of normalized
component laws, with index probabilities proportional to
`scale i * componentPartition i`. -/
theorem finitePositiveWeightMixtureProbability_eq_sum
    {ι α : Type}
    [Fintype ι]
    [Nonempty ι]
    [Fintype α]
    [Nonempty α]
    (scale : ι → ℝ)
    (weight : ι → α → ℝ)
    (hscale : ∀ i : ι, 0 < scale i)
    (hweight : ∀ i : ι, ∀ x : α, 0 < weight i x)
    (x : α) :
    (finitePositiveWeightMixtureProbabilityData
      scale weight hscale hweight).probability x =
      ∑ i : ι,
        (finitePositiveWeightMixtureIndexProbabilityData
          scale weight hscale hweight).probability i *
        (finitePositiveWeightMixtureComponentProbabilityData
          weight hweight i).probability x := by
  have hS :
      finitePositiveWeightMixtureIndexPartition scale weight ≠ 0 :=
    ne_of_gt
      (finitePositiveWeightMixtureIndexPartition_pos
        scale weight hscale hweight)
  have hZi (i : ι) :
      finitePositiveWeightMixtureComponentPartition weight i ≠ 0 :=
    ne_of_gt
      (finitePositiveWeightMixtureComponentPartition_pos weight hweight i)
  simp only [finitePositiveWeightMixtureProbabilityData,
    finitePositiveWeightMixtureIndexProbabilityData,
    finitePositiveWeightMixtureComponentProbabilityData,
    finiteRealWeightProbabilityData, finiteRealWeightProbability]
  rw [finitePositiveWeightMixtureRaw_partition]
  change
    finitePositiveWeightMixtureRaw scale weight x /
        finitePositiveWeightMixtureIndexPartition scale weight =
      ∑ i : ι,
        (finitePositiveWeightMixtureIndexWeight scale weight i /
          finitePositiveWeightMixtureIndexPartition scale weight) *
        (weight i x /
          finitePositiveWeightMixtureComponentPartition weight i)
  calc
    finitePositiveWeightMixtureRaw scale weight x /
        finitePositiveWeightMixtureIndexPartition scale weight =
      ∑ i : ι,
        (scale i * weight i x) /
          finitePositiveWeightMixtureIndexPartition scale weight := by
      unfold finitePositiveWeightMixtureRaw
      rw [Finset.sum_div]
    _ = ∑ i : ι,
        (finitePositiveWeightMixtureIndexWeight scale weight i /
          finitePositiveWeightMixtureIndexPartition scale weight) *
        (weight i x /
          finitePositiveWeightMixtureComponentPartition weight i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      unfold finitePositiveWeightMixtureIndexWeight
      field_simp [hZi i, hS]

end

end MathlibAnalytic
end MGAP4D
