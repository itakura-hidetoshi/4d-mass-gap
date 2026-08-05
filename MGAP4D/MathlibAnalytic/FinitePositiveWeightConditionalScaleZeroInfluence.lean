import MGAP4D.MathlibAnalytic.FinitePositiveWeightNonstrictInfluenceMatrix
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Multiplying a finite product weight by one scalar multiplies every one-site
partition by the same scalar. -/
theorem finitePositiveWeightSingleSitePartition_const_mul
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    (c : ℝ)
    (weight : (ι → G) → ℝ)
    (A : ι → G)
    (e : ι) :
    finitePositiveWeightSingleSitePartition
        (fun configuration => c * weight configuration) A e =
      c * finitePositiveWeightSingleSitePartition weight A e := by
  classical
  unfold finitePositiveWeightSingleSitePartition
  rw [Finset.mul_sum]

/-- A nonzero global scalar multiplier cancels from every one-site conditional
probability.  No positivity assumption is needed for this algebraic identity. -/
theorem finitePositiveWeightSingleSiteProbability_const_mul
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    (c : ℝ)
    (hc : c ≠ 0)
    (weight : (ι → G) → ℝ)
    (A : ι → G)
    (e : ι)
    (g : G) :
    finitePositiveWeightSingleSiteProbability
        (fun configuration => c * weight configuration) A e g =
      finitePositiveWeightSingleSiteProbability weight A e g := by
  rw [finitePositiveWeightSingleSiteProbability]
  rw [finitePositiveWeightSingleSiteProbability]
  rw [finitePositiveWeightSingleSitePartition_const_mul]
  by_cases hPartition :
      finitePositiveWeightSingleSitePartition weight A e = 0
  · simp [hPartition]
  · field_simp

/-- A nonzero global scalar multiplier leaves every one-site conditional
`L¹` distance unchanged. -/
theorem finitePositiveWeightSingleSiteConditionalL1_const_mul
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    (c : ℝ)
    (hc : c ≠ 0)
    (weight : (ι → G) → ℝ)
    (A B : ι → G)
    (target : ι) :
    finitePositiveWeightSingleSiteConditionalL1
        (fun configuration => c * weight configuration) A B target =
      finitePositiveWeightSingleSiteConditionalL1 weight A B target := by
  classical
  unfold finitePositiveWeightSingleSiteConditionalL1
  apply Finset.sum_congr rfl
  intro g _hg
  rw [finitePositiveWeightSingleSiteProbability_const_mul c hc]
  rw [finitePositiveWeightSingleSiteProbability_const_mul c hc]

/-- The exact finite set used by the canonical non-strict influence is
invariant under a nonzero global rescaling of the weight. -/
theorem finitePositiveWeightConditionalL1SourceValues_const_mul
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (c : ℝ)
    (hc : c ≠ 0)
    (weight : (ι → G) → ℝ)
    (target source : ι) :
    finitePositiveWeightConditionalL1SourceValues
        (fun configuration => c * weight configuration) target source =
      finitePositiveWeightConditionalL1SourceValues
        weight target source := by
  classical
  unfold finitePositiveWeightConditionalL1SourceValues
  apply congrArg (Finset.image · Finset.univ)
  funext pair
  by_cases hAgree : FiniteProductAgreeOff pair.1 pair.2 source
  · simp only [hAgree, if_true]
    exact finitePositiveWeightSingleSiteConditionalL1_const_mul
      c hc weight pair.1 pair.2 target
  · simp [hAgree]

/-- The canonical non-strict influence entry depends only on the projective
class of a finite positive weight: every nonzero global rescaling gives the
same exact entry. -/
theorem finitePositiveWeightCanonicalNonstrictInfluence_const_mul
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (c : ℝ)
    (hc : c ≠ 0)
    (weight : (ι → G) → ℝ)
    (target source : ι) :
    finitePositiveWeightCanonicalNonstrictInfluence
        (fun configuration => c * weight configuration) target source =
      finitePositiveWeightCanonicalNonstrictInfluence
        weight target source := by
  classical
  by_cases hEq : target = source
  · simp [finitePositiveWeightCanonicalNonstrictInfluence, hEq]
  · rw [finitePositiveWeightCanonicalNonstrictInfluence, if_neg hEq]
    rw [finitePositiveWeightCanonicalNonstrictInfluence, if_neg hEq]
    rw [finitePositiveWeightConditionalL1SourceValues_const_mul
      c hc weight target source]

/-- Every one-site conditional `L¹` distance of a configuration-independent
weight is exactly zero. -/
@[simp] theorem finitePositiveWeightSingleSiteConditionalL1_of_const
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    (c : ℝ)
    (A B : ι → G)
    (target : ι) :
    finitePositiveWeightSingleSiteConditionalL1
        (fun _configuration : ι → G => c) A B target = 0 := by
  classical
  unfold finitePositiveWeightSingleSiteConditionalL1
  apply Finset.sum_eq_zero
  intro g _hg
  congr 1
  unfold finitePositiveWeightSingleSiteProbability
    finitePositiveWeightSingleSitePartition
  rfl

/-- A configuration-independent finite product weight has exact zero canonical
non-strict influence at every ordered pair of coordinates. -/
@[simp] theorem finitePositiveWeightCanonicalNonstrictInfluence_of_const
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (c : ℝ)
    (target source : ι) :
    finitePositiveWeightCanonicalNonstrictInfluence
      (fun _configuration : ι → G => c) target source = 0 := by
  classical
  by_cases hEq : target = source
  · simp [finitePositiveWeightCanonicalNonstrictInfluence, hEq]
  · rw [finitePositiveWeightCanonicalNonstrictInfluence, if_neg hEq]
    apply le_antisymm
    · rw [Finset.max'_le_iff]
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨pair, _hPair, rfl⟩
      by_cases hAgree : FiniteProductAgreeOff pair.1 pair.2 source
      · simp [hAgree]
      · simp [hAgree]
    · exact Finset.le_max'
        (finitePositiveWeightConditionalL1SourceValues
          (fun _configuration : ι → G => c) target source)
        0
        (finitePositiveWeight_zero_mem_conditionalL1SourceValues
          (fun _configuration : ι → G => c) target source)

end

end MathlibAnalytic
end MGAP4D
