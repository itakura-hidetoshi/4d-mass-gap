import MGAP4D.MathlibAnalytic.FinitePositiveWeightSingleSiteConditional
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Agreement of two finite product configurations away from one coordinate. -/
def FiniteProductAgreeOff
    {ι G : Type}
    (A B : ι → G)
    (e : ι) : Prop :=
  ∀ i : ι, i ≠ e → A i = B i

/-- Replacing a coordinate by its current value does nothing. -/
@[simp] theorem finiteProductUpdate_current
    {ι G : Type}
    [DecidableEq ι]
    (A : ι → G)
    (e : ι) :
    Function.update A e (A e) = A := by
  funext i
  by_cases hie : i = e
  · subst i
    simp
  · simp [Function.update, hie]

/-- Configurations agreeing away from one coordinate differ by exactly one
coordinate replacement. -/
theorem finiteProductUpdate_right_of_agreeOff
    {ι G : Type}
    [DecidableEq ι]
    (A B : ι → G)
    (e : ι)
    (hAgree : FiniteProductAgreeOff A B e) :
    Function.update A e (B e) = B := by
  funext i
  by_cases hie : i = e
  · subst i
    simp
  · simp [Function.update, hie, hAgree i hie]

/-- Applying the same target-coordinate replacement preserves agreement away
from a declared source coordinate. -/
theorem finiteProductUpdate_agreeOff
    {ι G : Type}
    [DecidableEq ι]
    (A B : ι → G)
    (target source : ι)
    (g : G)
    (hAgree : FiniteProductAgreeOff A B source) :
    FiniteProductAgreeOff
      (Function.update A target g)
      (Function.update B target g)
      source := by
  intro i his
  by_cases hit : i = target
  · subst i
    simp
  · simp [Function.update, hit, hAgree i his]

/-- Real `L¹` distance between two one-site conditional laws of an arbitrary
strictly positive finite product weight.  This is twice the usual total
variation distance and is the normalization used by the generic influence
matrix below. -/
def finitePositiveWeightSingleSiteConditionalL1
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (A B : ι → G)
    (target : ι) : ℝ :=
  ∑ g : G,
    |finitePositiveWeightSingleSiteProbability weight A target g -
      finitePositiveWeightSingleSiteProbability weight B target g|

/-- Conditional `L¹` distance is nonnegative. -/
theorem finitePositiveWeightSingleSiteConditionalL1_nonneg
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (A B : ι → G)
    (target : ι) :
    0 ≤ finitePositiveWeightSingleSiteConditionalL1 weight A B target := by
  exact Finset.sum_nonneg fun g _hg => abs_nonneg _

/-- A positive-weight one-site conditional law depends only on the environment
away from the updated coordinate. -/
theorem finitePositiveWeightSingleSiteProbability_eq_of_agreeOff
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (A B : ι → G)
    (target : ι)
    (hAgree : FiniteProductAgreeOff A B target) :
    finitePositiveWeightSingleSiteProbability weight A target =
      finitePositiveWeightSingleSiteProbability weight B target := by
  funext g
  have hUpdate :
      ∀ h : G,
        Function.update A target h = Function.update B target h := by
    intro h
    funext i
    by_cases hit : i = target
    · subst i
      simp
    · simp [Function.update, hit, hAgree i hit]
  have hPartition :
      finitePositiveWeightSingleSitePartition weight A target =
        finitePositiveWeightSingleSitePartition weight B target := by
    unfold finitePositiveWeightSingleSitePartition
    apply Finset.sum_congr rfl
    intro h _hh
    rw [hUpdate h]
  unfold finitePositiveWeightSingleSiteProbability
  rw [hUpdate g, hPartition]

/-- Consequently the self-environment conditional `L¹` distance vanishes. -/
theorem finitePositiveWeightSingleSiteConditionalL1_eq_zero_of_agreeOff
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (A B : ι → G)
    (target : ι)
    (hAgree : FiniteProductAgreeOff A B target) :
    finitePositiveWeightSingleSiteConditionalL1 weight A B target = 0 := by
  unfold finitePositiveWeightSingleSiteConditionalL1
  rw [finitePositiveWeightSingleSiteProbability_eq_of_agreeOff
    weight A B target hAgree]
  simp

/-- Proof-relevant Dobrushin `L¹` influence data for an arbitrary strictly
positive finite product weight.  `influence target source` bounds the change of
the target conditional law when only the source coordinate is changed. -/
structure FinitePositiveWeightDobrushinL1MatrixData
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
  coefficient : ℝ
  coefficient_nonneg : 0 ≤ coefficient
  rowSum_le_coefficient :
    ∀ target : ι,
      ∑ source : ι, influence target source ≤ coefficient
  coefficient_lt_one : coefficient < 1

/-- Every declared influence row has sum strictly below one. -/
theorem finitePositiveWeightDobrushinL1_rowSum_lt_one
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    {weight : (ι → G) → ℝ}
    (D : FinitePositiveWeightDobrushinL1MatrixData weight)
    (target : ι) :
    (∑ source : ι, D.influence target source) < 1 :=
  lt_of_le_of_lt (D.rowSum_le_coefficient target) D.coefficient_lt_one

/-- Finite set of all exact one-coordinate fiber differences of an observable. -/
noncomputable def finiteProductSingleSiteDifferenceValues
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (f : (ι → G) → ℝ)
    (e : ι) : Finset ℝ := by
  classical
  exact Finset.univ.image fun x : (ι → G) × (G × G) =>
    |f (Function.update x.1 e x.2.1) -
      f (Function.update x.1 e x.2.2)|

/-- The finite fiber-difference set is nonempty. -/
theorem finiteProductSingleSiteDifferenceValues_nonempty
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (f : (ι → G) → ℝ)
    (e : ι) :
    (finiteProductSingleSiteDifferenceValues f e).Nonempty := by
  classical
  let A0 : ι → G := Classical.choice inferInstance
  let g0 : G := Classical.choice inferInstance
  refine ⟨0, ?_⟩
  unfold finiteProductSingleSiteDifferenceValues
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  refine ⟨(A0, (g0, g0)), ?_⟩
  simp

/-- Canonical global one-coordinate oscillation of a finite product
observable. -/
noncomputable def finiteProductCanonicalVariation
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (f : (ι → G) → ℝ)
    (e : ι) : ℝ :=
  (finiteProductSingleSiteDifferenceValues f e).max'
    (finiteProductSingleSiteDifferenceValues_nonempty f e)

/-- Every exact fiber difference is bounded by the canonical variation. -/
theorem finiteProduct_fiberDifference_abs_le_canonicalVariation
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (f : (ι → G) → ℝ)
    (A : ι → G)
    (e : ι)
    (g h : G) :
    |f (Function.update A e g) - f (Function.update A e h)| ≤
      finiteProductCanonicalVariation f e := by
  classical
  unfold finiteProductCanonicalVariation
  apply Finset.le_max'
  simp [finiteProductSingleSiteDifferenceValues]

/-- Canonical variation is nonnegative. -/
theorem finiteProductCanonicalVariation_nonneg
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (f : (ι → G) → ℝ)
    (e : ι) :
    0 ≤ finiteProductCanonicalVariation f e := by
  have h := finiteProduct_fiberDifference_abs_le_canonicalVariation
    f (Classical.choice (inferInstance : Nonempty (ι → G))) e
      (Classical.choice (inferInstance : Nonempty G))
      (Classical.choice (inferInstance : Nonempty G))
  simpa using h

/-- Canonical variation controls arbitrary configurations differing only at the
selected coordinate. -/
theorem finiteProduct_difference_abs_le_canonicalVariation
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (f : (ι → G) → ℝ)
    (e : ι)
    (A B : ι → G)
    (hAgree : FiniteProductAgreeOff A B e) :
    |f A - f B| ≤ finiteProductCanonicalVariation f e := by
  simpa [finiteProductUpdate_current,
    finiteProductUpdate_right_of_agreeOff A B e hAgree] using
    finiteProduct_fiberDifference_abs_le_canonicalVariation
      f A e (A e) (B e)

/-- Total canonical coordinate variation. -/
noncomputable def finiteProductCanonicalTotalVariation
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (f : (ι → G) → ℝ) : ℝ :=
  ∑ e : ι, finiteProductCanonicalVariation f e

/-- Total canonical variation is nonnegative. -/
theorem finiteProductCanonicalTotalVariation_nonneg
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (f : (ι → G) → ℝ) :
    0 ≤ finiteProductCanonicalTotalVariation f := by
  exact Finset.sum_nonneg fun e _he =>
    finiteProductCanonicalVariation_nonneg f e

/-- A real finite probability average of a uniformly bounded test function is
bounded by the same radius. -/
theorem finiteRealProbability_abs_expectation_le
    {G : Type}
    [Fintype G]
    (prob : G → ℝ)
    (hprob_nonneg : ∀ g : G, 0 ≤ prob g)
    (hprob_sum : ∑ g : G, prob g = 1)
    (u : G → ℝ)
    (M : ℝ)
    (hu : ∀ g : G, |u g| ≤ M) :
    |∑ g : G, prob g * u g| ≤ M := by
  calc
    |∑ g : G, prob g * u g| ≤
        ∑ g : G, |prob g * u g| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ g : G, prob g * |u g| := by
      apply Finset.sum_congr rfl
      intro g _hg
      rw [abs_mul, abs_of_nonneg (hprob_nonneg g)]
    _ ≤ ∑ g : G, prob g * M := by
      apply Finset.sum_le_sum
      intro g _hg
      exact mul_le_mul_of_nonneg_left (hu g) (hprob_nonneg g)
    _ = M := by
      rw [← Finset.sum_mul, hprob_sum, one_mul]

/-- A common bounded test function converts conditional `L¹` distance into an
expectation difference bound. -/
theorem finiteRealProbability_expectation_difference_abs_le_l1_mul
    {G : Type}
    [Fintype G]
    [Nonempty G]
    (p q : G → ℝ)
    (u : G → ℝ)
    (M : ℝ)
    (hu : ∀ g h : G, |u g - u h| ≤ M)
    (hp_sum : ∑ g : G, p g = 1)
    (hq_sum : ∑ g : G, q g = 1) :
    |(∑ g : G, p g * u g) - ∑ g : G, q g * u g| ≤
      (∑ g : G, |p g - q g|) * M := by
  classical
  let g0 : G := Classical.choice inferInstance
  have hzero : ∑ g : G, (p g - q g) = 0 := by
    rw [Finset.sum_sub_distrib, hp_sum, hq_sum]
    ring
  have hcenter :
      (∑ g : G, p g * u g) - ∑ g : G, q g * u g =
        ∑ g : G, (p g - q g) * (u g - u g0) := by
    calc
      (∑ g : G, p g * u g) - ∑ g : G, q g * u g =
          ∑ g : G, (p g - q g) * u g := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro g _hg
        ring
      _ = ∑ g : G, (p g - q g) * (u g - u g0) := by
        symm
        calc
          (∑ g : G, (p g - q g) * (u g - u g0)) =
              ∑ g : G,
                ((p g - q g) * u g - (p g - q g) * u g0) := by
            apply Finset.sum_congr rfl
            intro g _hg
            ring
          _ = (∑ g : G, (p g - q g) * u g) -
              ∑ g : G, (p g - q g) * u g0 := by
            rw [Finset.sum_sub_distrib]
          _ = (∑ g : G, (p g - q g) * u g) -
              (∑ g : G, (p g - q g)) * u g0 := by
            rw [Finset.sum_mul]
          _ = ∑ g : G, (p g - q g) * u g := by
            rw [hzero, zero_mul, sub_zero]
  rw [hcenter]
  calc
    |∑ g : G, (p g - q g) * (u g - u g0)| ≤
        ∑ g : G, |(p g - q g) * (u g - u g0)| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ g : G, |p g - q g| * |u g - u g0| := by
      apply Finset.sum_congr rfl
      intro g _hg
      rw [abs_mul]
    _ ≤ ∑ g : G, |p g - q g| * M := by
      apply Finset.sum_le_sum
      intro g _hg
      exact mul_le_mul_of_nonneg_left (hu g g0) (abs_nonneg _)
    _ = (∑ g : G, |p g - q g|) * M := by
      rw [Finset.sum_mul]

/-- Conditional expectation is invariant under changes of the current value at
the coordinate being resampled. -/
theorem finitePositiveWeightSingleSiteExpectation_eq_of_agreeOff
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (f : (ι → G) → ℝ)
    (A B : ι → G)
    (target : ι)
    (hAgree : FiniteProductAgreeOff A B target) :
    finitePositiveWeightSingleSiteExpectation weight f A target =
      finitePositiveWeightSingleSiteExpectation weight f B target := by
  have hProb := finitePositiveWeightSingleSiteProbability_eq_of_agreeOff
    weight A B target hAgree
  unfold finitePositiveWeightSingleSiteExpectation
  rw [hProb]
  apply Finset.sum_congr rfl
  intro g _hg
  have hUpdate :
      Function.update A target g = Function.update B target g := by
    funext i
    by_cases hit : i = target
    · subst i
      simp
    · simp [Function.update, hit, hAgree i hit]
  rw [hUpdate]

/-- Generic local Dobrushin propagation for a one-site conditional
expectation. -/
theorem finitePositiveWeightDobrushin_singleSiteExpectation_difference_abs_le
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (D : FinitePositiveWeightDobrushinL1MatrixData weight)
    (f : (ι → G) → ℝ)
    (target source : ι)
    (A B : ι → G)
    (hAgree : FiniteProductAgreeOff A B source) :
    |finitePositiveWeightSingleSiteExpectation weight f A target -
        finitePositiveWeightSingleSiteExpectation weight f B target| ≤
      if source = target then 0
      else finiteProductCanonicalVariation f source +
        D.influence target source * finiteProductCanonicalVariation f target := by
  classical
  by_cases hst : source = target
  · subst source
    rw [finitePositiveWeightSingleSiteExpectation_eq_of_agreeOff
      weight f A B target hAgree]
    simp
  · simp only [hst, if_false]
    let pA := finitePositiveWeightSingleSiteProbability weight A target
    let pB := finitePositiveWeightSingleSiteProbability weight B target
    let uA : G → ℝ := fun g => f (Function.update A target g)
    let uB : G → ℝ := fun g => f (Function.update B target g)
    have hpA_nonneg : ∀ g : G, 0 ≤ pA g := by
      intro g
      exact le_of_lt
        (finitePositiveWeightSingleSiteProbability_pos weight hweight A target g)
    have hpA_sum : ∑ g : G, pA g = 1 := by
      simpa [pA] using
        finitePositiveWeightSingleSiteProbability_sum_eq_one
          weight hweight A target
    have hpB_sum : ∑ g : G, pB g = 1 := by
      simpa [pB] using
        finitePositiveWeightSingleSiteProbability_sum_eq_one
          weight hweight B target
    have hDirect :
        |∑ g : G, pA g * (uA g - uB g)| ≤
          finiteProductCanonicalVariation f source := by
      apply finiteRealProbability_abs_expectation_le
        pA hpA_nonneg hpA_sum
      intro g
      exact finiteProduct_difference_abs_le_canonicalVariation
        f source
        (Function.update A target g)
        (Function.update B target g)
        (finiteProductUpdate_agreeOff A B target source g hAgree)
    have hLaw :
        |(∑ g : G, pA g * uB g) -
            ∑ g : G, pB g * uB g| ≤
          D.influence target source *
            finiteProductCanonicalVariation f target := by
      have hOsc : ∀ g h : G,
          |uB g - uB h| ≤ finiteProductCanonicalVariation f target := by
        intro g h
        exact finiteProduct_fiberDifference_abs_le_canonicalVariation
          f B target g h
      have hL1 := D.conditionalL1_le target source A B hAgree
      calc
        |(∑ g : G, pA g * uB g) -
            ∑ g : G, pB g * uB g| ≤
          finitePositiveWeightSingleSiteConditionalL1 weight A B target *
            finiteProductCanonicalVariation f target := by
          simpa [pA, pB, uB,
            finitePositiveWeightSingleSiteConditionalL1] using
            finiteRealProbability_expectation_difference_abs_le_l1_mul
              pA pB uB (finiteProductCanonicalVariation f target)
              hOsc hpA_sum hpB_sum
        _ ≤ D.influence target source *
            finiteProductCanonicalVariation f target :=
          mul_le_mul_of_nonneg_right hL1
            (finiteProductCanonicalVariation_nonneg f target)
    unfold finitePositiveWeightSingleSiteExpectation
    change
      |(∑ g : G, pA g * uA g) -
          ∑ g : G, pB g * uB g| ≤ _
    have hSplit :
        (∑ g : G, pA g * uA g) -
            ∑ g : G, pB g * uB g =
          (∑ g : G, pA g * (uA g - uB g)) +
            ((∑ g : G, pA g * uB g) -
              ∑ g : G, pB g * uB g) := by
      calc
        (∑ g : G, pA g * uA g) -
            ∑ g : G, pB g * uB g =
          ((∑ g : G, pA g * uA g) -
            ∑ g : G, pA g * uB g) +
            ((∑ g : G, pA g * uB g) -
              ∑ g : G, pB g * uB g) := by ring
        _ = (∑ g : G, pA g * (uA g - uB g)) +
            ((∑ g : G, pA g * uB g) -
              ∑ g : G, pB g * uB g) := by
          congr 1
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro g _hg
          ring
    rw [hSplit]
    exact le_trans (abs_add_le _ _) (add_le_add hDirect hLaw)

end

end MathlibAnalytic
end MGAP4D
