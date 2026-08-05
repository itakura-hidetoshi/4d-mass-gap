import MGAP4D.MathlibAnalytic.FinitePositiveWeightBidirectionalDobrushinL1Matrix
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Replace the coordinates in `s` by their values in `B`, retaining `A`
outside `s`. -/
def finiteProductReplaceOn
    {ι G : Type}
    [DecidableEq ι]
    (A B : ι → G)
    (s : Finset ι) : ι → G :=
  fun i => if i ∈ s then B i else A i

@[simp] theorem finiteProductReplaceOn_empty
    {ι G : Type}
    [DecidableEq ι]
    (A B : ι → G) :
    finiteProductReplaceOn A B ∅ = A := by
  funext i
  simp [finiteProductReplaceOn]

@[simp] theorem finiteProductReplaceOn_univ
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    (A B : ι → G) :
    finiteProductReplaceOn A B Finset.univ = B := by
  funext i
  simp [finiteProductReplaceOn]

/-- Adding one replacement coordinate changes no other coordinate. -/
theorem finiteProductReplaceOn_agreeOff_insert
    {ι G : Type}
    [DecidableEq ι]
    (A B : ι → G)
    (s : Finset ι)
    (source : ι) :
    FiniteProductAgreeOff
      (finiteProductReplaceOn A B s)
      (finiteProductReplaceOn A B (insert source s))
      source := by
  intro i hi
  simp [finiteProductReplaceOn, hi]

/-- Triangle inequality for conditional `L¹` distance. -/
theorem finitePositiveWeightSingleSiteConditionalL1_triangle
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (A B C : ι → G)
    (target : ι) :
    finitePositiveWeightSingleSiteConditionalL1 weight A C target ≤
      finitePositiveWeightSingleSiteConditionalL1 weight A B target +
        finitePositiveWeightSingleSiteConditionalL1 weight B C target := by
  unfold finitePositiveWeightSingleSiteConditionalL1
  calc
    (∑ g : G,
      |finitePositiveWeightSingleSiteProbability weight A target g -
        finitePositiveWeightSingleSiteProbability weight C target g|) ≤
        ∑ g : G,
          (|finitePositiveWeightSingleSiteProbability weight A target g -
              finitePositiveWeightSingleSiteProbability weight B target g| +
            |finitePositiveWeightSingleSiteProbability weight B target g -
              finitePositiveWeightSingleSiteProbability weight C target g|) := by
      apply Finset.sum_le_sum
      intro g _hg
      have hDecompose :
          finitePositiveWeightSingleSiteProbability weight A target g -
              finitePositiveWeightSingleSiteProbability weight C target g =
            (finitePositiveWeightSingleSiteProbability weight A target g -
              finitePositiveWeightSingleSiteProbability weight B target g) +
            (finitePositiveWeightSingleSiteProbability weight B target g -
              finitePositiveWeightSingleSiteProbability weight C target g) := by
        ring
      rw [hDecompose]
      exact abs_add _ _
    _ =
        (∑ g : G,
          |finitePositiveWeightSingleSiteProbability weight A target g -
            finitePositiveWeightSingleSiteProbability weight B target g|) +
        ∑ g : G,
          |finitePositiveWeightSingleSiteProbability weight B target g -
            finitePositiveWeightSingleSiteProbability weight C target g| :=
      Finset.sum_add_distrib

/-- Replacing a finite set of coordinates produces conditional `L¹` change
bounded by the corresponding finite influence sum. -/
theorem finitePositiveWeightNonstrict_conditionalL1_replaceOn_le_sum
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    {weight : (ι → G) → ℝ}
    (D : FinitePositiveWeightNonstrictL1MatrixData weight)
    (A B : ι → G)
    (target : ι)
    (s : Finset ι) :
    finitePositiveWeightSingleSiteConditionalL1
        weight A (finiteProductReplaceOn A B s) target ≤
      ∑ source ∈ s, D.influence target source := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [finitePositiveWeightSingleSiteConditionalL1,
        finiteProductReplaceOn]
  | @insert source s hSource ih =>
      have hOne :
          finitePositiveWeightSingleSiteConditionalL1
              weight
              (finiteProductReplaceOn A B s)
              (finiteProductReplaceOn A B (insert source s))
              target ≤
            D.influence target source :=
        D.conditionalL1_le target source
          (finiteProductReplaceOn A B s)
          (finiteProductReplaceOn A B (insert source s))
          (finiteProductReplaceOn_agreeOff_insert A B s source)
      calc
        finitePositiveWeightSingleSiteConditionalL1
            weight A (finiteProductReplaceOn A B (insert source s)) target ≤
          finitePositiveWeightSingleSiteConditionalL1
              weight A (finiteProductReplaceOn A B s) target +
            finitePositiveWeightSingleSiteConditionalL1
              weight
              (finiteProductReplaceOn A B s)
              (finiteProductReplaceOn A B (insert source s))
              target :=
          finitePositiveWeightSingleSiteConditionalL1_triangle
            weight A (finiteProductReplaceOn A B s)
              (finiteProductReplaceOn A B (insert source s)) target
        _ ≤ (∑ e ∈ s, D.influence target e) +
              D.influence target source :=
          add_le_add ih hOne
        _ = ∑ e ∈ insert source s, D.influence target e := by
          rw [Finset.sum_insert hSource]
          ring

/-- Coordinates on which two finite product configurations disagree. -/
def finiteProductDisagreementFinset
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype ι]
    (A B : ι → G) : Finset ι :=
  Finset.univ.filter fun i => A i ≠ B i

/-- Replacing exactly the disagreement coordinates transforms `A` into `B`. -/
theorem finiteProductReplaceOn_disagreementFinset
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype ι]
    (A B : ι → G) :
    finiteProductReplaceOn A B
      (finiteProductDisagreementFinset A B) = B := by
  funext i
  by_cases hEq : A i = B i
  · simp [finiteProductReplaceOn, finiteProductDisagreementFinset, hEq]
  · simp [finiteProductReplaceOn, finiteProductDisagreementFinset, hEq]

/-- Arbitrary-environment conditional `L¹` change is bounded by the influence
sum over the coordinates where the environments actually differ. -/
theorem finitePositiveWeightNonstrict_conditionalL1_le_disagreementInfluenceSum
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype ι]
    [Fintype G]
    {weight : (ι → G) → ℝ}
    (D : FinitePositiveWeightNonstrictL1MatrixData weight)
    (A B : ι → G)
    (target : ι) :
    finitePositiveWeightSingleSiteConditionalL1 weight A B target ≤
      ∑ source ∈ finiteProductDisagreementFinset A B,
        D.influence target source := by
  simpa [finiteProductReplaceOn_disagreementFinset A B] using
    finitePositiveWeightNonstrict_conditionalL1_replaceOn_le_sum
      D A B target (finiteProductDisagreementFinset A B)

/-- Real Hamming distance on a finite product configuration space. -/
def finiteProductHammingDistanceReal
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype ι]
    (A B : ι → G) : ℝ :=
  ((finiteProductDisagreementFinset A B).card : ℝ)

/-- The half-scaled bidirectional coefficient governing the canonical overlap
coupling is nonnegative. -/
theorem FinitePositiveWeightBidirectionalDobrushinL1MatrixData.halfCoefficient_nonneg
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    {weight : (ι → G) → ℝ}
    (B : FinitePositiveWeightBidirectionalDobrushinL1MatrixData weight) :
    0 ≤ (2 : ℝ)⁻¹ * B.coefficient := by
  positivity

/-- The half-scaled bidirectional coefficient is strictly below one. -/
theorem FinitePositiveWeightBidirectionalDobrushinL1MatrixData.halfCoefficient_lt_one
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    {weight : (ι → G) → ℝ}
    (B : FinitePositiveWeightBidirectionalDobrushinL1MatrixData weight) :
    (2 : ℝ)⁻¹ * B.coefficient < 1 := by
  have hNonneg := B.coefficient_nonneg
  have hLt := B.coefficient_lt_one
  norm_num at *
  nlinarith

/-- The canonical parallel product coupling contracts total coordinate
disagreement by one half of the common bidirectional influence coefficient. -/
theorem FinitePositiveWeightBidirectionalDobrushinL1MatrixData.parallelTotalCoordinateDisagreement_le_halfCoefficient_mul_hamming
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    {weight : (ι → G) → ℝ}
    (B : FinitePositiveWeightBidirectionalDobrushinL1MatrixData weight)
    (hweight : ∀ configuration : ι → G, 0 < weight configuration)
    (A C : ι → G) :
    finitePositiveWeightParallelTotalCoordinateDisagreement
        weight hweight A C ≤
      ((2 : ℝ)⁻¹ * B.coefficient) *
        finiteProductHammingDistanceReal A C := by
  let S := finiteProductDisagreementFinset A C
  have hTarget
      (target : ι) :
      finitePositiveWeightSingleSiteConditionalL1 weight A C target ≤
        ∑ source ∈ S, B.influence target source := by
    exact
      finitePositiveWeightNonstrict_conditionalL1_le_disagreementInfluenceSum
        B.toNonstrictL1MatrixData A C target
  have hTargetSum :
      (∑ target : ι,
        finitePositiveWeightSingleSiteConditionalL1 weight A C target) ≤
      ∑ target : ι, ∑ source ∈ S, B.influence target source := by
    exact Finset.sum_le_sum fun target _hTarget => hTarget target
  have hColumns :
      (∑ target : ι, ∑ source ∈ S, B.influence target source) ≤
        ∑ source ∈ S, B.coefficient := by
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun source _hSource =>
      B.columnSum_le_coefficient source
  calc
    finitePositiveWeightParallelTotalCoordinateDisagreement
        weight hweight A C =
      (2 : ℝ)⁻¹ *
        ∑ target : ι,
          finitePositiveWeightSingleSiteConditionalL1 weight A C target :=
      finitePositiveWeightParallelTotalCoordinateDisagreement_eq_half_sum
        weight hweight A C
    _ ≤ (2 : ℝ)⁻¹ *
        (∑ target : ι, ∑ source ∈ S,
          B.influence target source) :=
      mul_le_mul_of_nonneg_left hTargetSum (by positivity)
    _ ≤ (2 : ℝ)⁻¹ * (∑ source ∈ S, B.coefficient) :=
      mul_le_mul_of_nonneg_left hColumns (by positivity)
    _ = ((2 : ℝ)⁻¹ * B.coefficient) *
        finiteProductHammingDistanceReal A C := by
      simp [S, finiteProductHammingDistanceReal]
      ring

end

end MathlibAnalytic
end MGAP4D
