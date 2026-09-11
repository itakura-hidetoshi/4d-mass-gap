import MGAP4D.MathlibAnalytic.FinitePositiveWeightDobrushinInfluence
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Proof-relevant conditional `L¹` influence data without a strict row-sum
assumption.  Unlike `FinitePositiveWeightDobrushinL1MatrixData`, this structure
exists canonically for every strictly positive finite product weight and can
therefore be used as the non-circular starting point of a bootstrap. -/
structure FinitePositiveWeightNonstrictL1MatrixData
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ) where
  influence : ι → ι → ℝ
  influence_nonneg :
    ∀ target source : ι, 0 ≤ influence target source
  influence_diagonal_zero :
    ∀ e : ι, influence e e = 0
  conditionalL1_le :
    ∀ (target source : ι) (A B : ι → G),
      FiniteProductAgreeOff A B source →
        finitePositiveWeightSingleSiteConditionalL1 weight A B target ≤
          influence target source

/-- Forget the strict coefficient fields of a Dobrushin matrix while retaining
its complete entrywise conditional-influence content. -/
noncomputable def
    FinitePositiveWeightDobrushinL1MatrixData.toNonstrict
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    {weight : (ι → G) → ℝ}
    (D : FinitePositiveWeightDobrushinL1MatrixData weight) :
    FinitePositiveWeightNonstrictL1MatrixData weight :=
  { influence := D.influence
    influence_nonneg := D.influence_nonneg
    influence_diagonal_zero := D.influence_diagonal_zero
    conditionalL1_le := D.conditionalL1_le }

/-- All one-source environment pairs, encoded by their conditional `L¹`
difference when they agree away from the declared source and by zero
otherwise.  Taking the finite maximum produces a canonical, non-circular
influence entry. -/
noncomputable def finitePositiveWeightConditionalL1SourceValues
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (target source : ι) : Finset ℝ := by
  classical
  exact Finset.univ.image fun pair : (ι → G) × (ι → G) =>
    if FiniteProductAgreeOff pair.1 pair.2 source then
      finitePositiveWeightSingleSiteConditionalL1
        weight pair.1 pair.2 target
    else 0

/-- Zero belongs to every source-value set, by taking the same environment on
both sides. -/
theorem finitePositiveWeight_zero_mem_conditionalL1SourceValues
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (target source : ι) :
    0 ∈ finitePositiveWeightConditionalL1SourceValues
      weight target source := by
  classical
  let g₀ : G := Classical.choice (inferInstance : Nonempty G)
  let A₀ : ι → G := fun _ => g₀
  unfold finitePositiveWeightConditionalL1SourceValues
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  refine ⟨(A₀, A₀), ?_⟩
  simp [FiniteProductAgreeOff,
    finitePositiveWeightSingleSiteConditionalL1]

/-- The finite source-value set is nonempty. -/
theorem finitePositiveWeightConditionalL1SourceValues_nonempty
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (target source : ι) :
    (finitePositiveWeightConditionalL1SourceValues
      weight target source).Nonempty :=
  ⟨0,
    finitePositiveWeight_zero_mem_conditionalL1SourceValues
      weight target source⟩

/-- Canonical source-specific conditional influence: exact zero on the
diagonal and the finite maximum of all admissible one-source conditional
changes off the diagonal. -/
noncomputable def finitePositiveWeightCanonicalNonstrictInfluence
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (target source : ι) : ℝ :=
  if target = source then 0 else
    (finitePositiveWeightConditionalL1SourceValues
      weight target source).max'
        (finitePositiveWeightConditionalL1SourceValues_nonempty
          weight target source)

/-- Canonical non-strict influence is nonnegative. -/
theorem finitePositiveWeightCanonicalNonstrictInfluence_nonneg
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (target source : ι) :
    0 ≤ finitePositiveWeightCanonicalNonstrictInfluence
      weight target source := by
  by_cases hEq : target = source
  · simp [finitePositiveWeightCanonicalNonstrictInfluence, hEq]
  · rw [finitePositiveWeightCanonicalNonstrictInfluence, if_neg hEq]
    exact Finset.le_max'
      (finitePositiveWeightConditionalL1SourceValues
        weight target source)
      0
      (finitePositiveWeight_zero_mem_conditionalL1SourceValues
        weight target source)

/-- Canonical non-strict influence has exact zero diagonal. -/
@[simp] theorem finitePositiveWeightCanonicalNonstrictInfluence_diagonal
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (e : ι) :
    finitePositiveWeightCanonicalNonstrictInfluence weight e e = 0 := by
  simp [finitePositiveWeightCanonicalNonstrictInfluence]

/-- The canonical finite maximum bounds every actual one-source conditional
change. -/
theorem finitePositiveWeightSingleSiteConditionalL1_le_canonicalNonstrictInfluence
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (target source : ι)
    (A B : ι → G)
    (hAgree : FiniteProductAgreeOff A B source) :
    finitePositiveWeightSingleSiteConditionalL1 weight A B target ≤
      finitePositiveWeightCanonicalNonstrictInfluence
        weight target source := by
  by_cases hEq : target = source
  · subst source
    rw [finitePositiveWeightSingleSiteConditionalL1_eq_zero_of_agreeOff
      weight A B target hAgree]
    simp
  · rw [finitePositiveWeightCanonicalNonstrictInfluence, if_neg hEq]
    apply Finset.le_max'
    unfold finitePositiveWeightConditionalL1SourceValues
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨(A, B), ?_⟩
    simp [hAgree]

/-- Every positive-weight conditional `L¹` distance is at most two. -/
theorem finitePositiveWeightSingleSiteConditionalL1_le_two
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (A B : ι → G)
    (target : ι) :
    finitePositiveWeightSingleSiteConditionalL1 weight A B target ≤ 2 := by
  let p : G → ℝ :=
    finitePositiveWeightSingleSiteProbability weight A target
  let q : G → ℝ :=
    finitePositiveWeightSingleSiteProbability weight B target
  have hpNonneg : ∀ g : G, 0 ≤ p g := by
    intro g
    exact le_of_lt
      (finitePositiveWeightSingleSiteProbability_pos
        weight hweight A target g)
  have hqNonneg : ∀ g : G, 0 ≤ q g := by
    intro g
    exact le_of_lt
      (finitePositiveWeightSingleSiteProbability_pos
        weight hweight B target g)
  have hpSum : ∑ g : G, p g = 1 := by
    simpa [p] using
      finitePositiveWeightSingleSiteProbability_sum_eq_one
        weight hweight A target
  have hqSum : ∑ g : G, q g = 1 := by
    simpa [q] using
      finitePositiveWeightSingleSiteProbability_sum_eq_one
        weight hweight B target
  unfold finitePositiveWeightSingleSiteConditionalL1
  change (∑ g : G, |p g - q g|) ≤ 2
  calc
    (∑ g : G, |p g - q g|) ≤
        ∑ g : G, (p g + q g) := by
      apply Finset.sum_le_sum
      intro g _hg
      rw [abs_le]
      constructor <;> linarith [hpNonneg g, hqNonneg g]
    _ = 2 := by
      rw [Finset.sum_add_distrib, hpSum, hqSum]
      norm_num

/-- The canonical non-strict influence entry is universally bounded by two. -/
theorem finitePositiveWeightCanonicalNonstrictInfluence_le_two
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (target source : ι) :
    finitePositiveWeightCanonicalNonstrictInfluence
      weight target source ≤ 2 := by
  by_cases hEq : target = source
  · simp [finitePositiveWeightCanonicalNonstrictInfluence, hEq]
  · rw [finitePositiveWeightCanonicalNonstrictInfluence, if_neg hEq]
    rw [Finset.max'_le_iff]
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨pair, _hPair, rfl⟩
    by_cases hAgree : FiniteProductAgreeOff pair.1 pair.2 source
    · simpa [hAgree] using
        finitePositiveWeightSingleSiteConditionalL1_le_two
          weight hweight pair.1 pair.2 target
    · simp [hAgree]

/-- Every positive finite product weight has a canonical non-strict influence
matrix, with no row-sum hypothesis. -/
noncomputable def finitePositiveWeightCanonicalNonstrictL1MatrixData
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ) :
    FinitePositiveWeightNonstrictL1MatrixData weight :=
  { influence := finitePositiveWeightCanonicalNonstrictInfluence weight
    influence_nonneg :=
      finitePositiveWeightCanonicalNonstrictInfluence_nonneg weight
    influence_diagonal_zero :=
      finitePositiveWeightCanonicalNonstrictInfluence_diagonal weight
    conditionalL1_le := fun target source A B hAgree =>
      finitePositiveWeightSingleSiteConditionalL1_le_canonicalNonstrictInfluence
        weight target source A B hAgree }

/-- Row sum of a non-strict influence matrix. -/
def finitePositiveWeightNonstrictInfluenceRowSum
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    {weight : (ι → G) → ℝ}
    (D : FinitePositiveWeightNonstrictL1MatrixData weight)
    (target : ι) : ℝ :=
  ∑ source : ι, D.influence target source

/-- Column sum of a non-strict influence matrix. -/
def finitePositiveWeightNonstrictInfluenceColumnSum
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    {weight : (ι → G) → ℝ}
    (D : FinitePositiveWeightNonstrictL1MatrixData weight)
    (source : ι) : ℝ :=
  ∑ target : ι, D.influence target source

/-- Entrywise domination of a concrete non-strict influence matrix by a
weight-independent nonnegative kernel. -/
def FinitePositiveWeightNonstrictInfluenceDominatedBy
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    {weight : (ι → G) → ℝ}
    (D : FinitePositiveWeightNonstrictL1MatrixData weight)
    (kernel : ι → ι → ℝ) : Prop :=
  ∀ target source : ι,
    D.influence target source ≤ kernel target source

/-- A non-strict matrix plus a strict uniform row bound canonically becomes
the existing Dobrushin matrix consumed by the spectral-gap spine. -/
noncomputable def
    FinitePositiveWeightNonstrictL1MatrixData.toDobrushinL1MatrixData
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    {weight : (ι → G) → ℝ}
    (D : FinitePositiveWeightNonstrictL1MatrixData weight)
    (coefficient : ℝ)
    (hCoefficientNonneg : 0 ≤ coefficient)
    (hRowSum :
      ∀ target : ι,
        finitePositiveWeightNonstrictInfluenceRowSum D target ≤ coefficient)
    (hCoefficientLtOne : coefficient < 1) :
    FinitePositiveWeightDobrushinL1MatrixData weight :=
  { influence := D.influence
    influence_nonneg := D.influence_nonneg
    influence_diagonal_zero := D.influence_diagonal_zero
    conditionalL1_le := D.conditionalL1_le
    coefficient := coefficient
    coefficient_nonneg := hCoefficientNonneg
    rowSum_le_coefficient := hRowSum
    coefficient_lt_one := hCoefficientLtOne }

end

end MathlibAnalytic
end MGAP4D
