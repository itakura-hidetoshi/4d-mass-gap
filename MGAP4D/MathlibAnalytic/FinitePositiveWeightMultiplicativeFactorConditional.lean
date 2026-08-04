import MGAP4D.MathlibAnalytic.FinitePositiveWeightConditionalCrossRatioInfluence
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Pointwise product of two finite product weights. -/
def finitePositiveWeightProduct
    {ι G : Type}
    (left right : (ι → G) → ℝ)
    (A : ι → G) : ℝ :=
  left A * right A

/-- A function on product configurations is independent of one coordinate
fiber when replacing that coordinate never changes its value. -/
def FiniteProductFunctionIndependentOfCoordinate
    {ι G : Type}
    [DecidableEq ι]
    (factor : (ι → G) → ℝ)
    (target : ι) : Prop :=
  ∀ (A : ι → G) (g : G),
    factor (Function.update A target g) = factor A

/-- A fiber-independent factor pulls out of the one-site partition function. -/
theorem finitePositiveWeightProduct_singleSitePartition_eq
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    (left right : (ι → G) → ℝ)
    (A : ι → G)
    (target : ι)
    (hRight : FiniteProductFunctionIndependentOfCoordinate right target) :
    finitePositiveWeightSingleSitePartition
        (finitePositiveWeightProduct left right) A target =
      finitePositiveWeightSingleSitePartition left A target * right A := by
  classical
  unfold finitePositiveWeightSingleSitePartition finitePositiveWeightProduct
  simp_rw [hRight A]
  exact Finset.sum_mul.symm

/-- Multiplication by a strictly positive factor independent of the updated
coordinate leaves the one-site conditional law exactly unchanged. -/
theorem finitePositiveWeightProduct_singleSiteProbability_eq_left
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    [Nonempty G]
    (left right : (ι → G) → ℝ)
    (hLeft : ∀ A : ι → G, 0 < left A)
    (hRightPos : ∀ A : ι → G, 0 < right A)
    (A : ι → G)
    (target : ι)
    (hRight : FiniteProductFunctionIndependentOfCoordinate right target)
    (g : G) :
    finitePositiveWeightSingleSiteProbability
        (finitePositiveWeightProduct left right) A target g =
      finitePositiveWeightSingleSiteProbability left A target g := by
  unfold finitePositiveWeightSingleSiteProbability
  rw [finitePositiveWeightProduct_singleSitePartition_eq
    left right A target hRight]
  unfold finitePositiveWeightProduct
  rw [hRight A g]
  have hZ :
      finitePositiveWeightSingleSitePartition left A target ≠ 0 :=
    ne_of_gt
      (finitePositiveWeightSingleSitePartition_pos
        left hLeft A target)
  have hFactor : right A ≠ 0 := ne_of_gt (hRightPos A)
  field_simp [hZ, hFactor]

/-- Consequently every one-site conditional expectation is unchanged by a
strictly positive fiber-independent factor. -/
theorem finitePositiveWeightProduct_singleSiteExpectation_eq_left
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    [Nonempty G]
    (left right : (ι → G) → ℝ)
    (hLeft : ∀ A : ι → G, 0 < left A)
    (hRightPos : ∀ A : ι → G, 0 < right A)
    (f : (ι → G) → ℝ)
    (A : ι → G)
    (target : ι)
    (hRight : FiniteProductFunctionIndependentOfCoordinate right target) :
    finitePositiveWeightSingleSiteExpectation
        (finitePositiveWeightProduct left right) f A target =
      finitePositiveWeightSingleSiteExpectation left f A target := by
  unfold finitePositiveWeightSingleSiteExpectation
  apply Finset.sum_congr rfl
  intro g _hg
  rw [finitePositiveWeightProduct_singleSiteProbability_eq_left
    left right hLeft hRightPos A target hRight g]

/-- A factor independent of a target fiber has exact four-point cross ratio
one at that target. -/
theorem finiteProductFunctionIndependentOfCoordinate_crossRatio_one
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    (factor : (ι → G) → ℝ)
    (A B : ι → G)
    (target : ι)
    (hFactor : FiniteProductFunctionIndependentOfCoordinate factor target) :
    FinitePositiveWeightSingleSiteCrossRatioBound
      factor A B target 1 := by
  intro g h
  rw [hFactor A g, hFactor B h, hFactor B g, hFactor A h]
  ring

/-- Four-point cross-ratio bounds multiply under pointwise products of
nonnegative weights. -/
theorem finitePositiveWeightProduct_singleSiteCrossRatioBound
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    (left right : (ι → G) → ℝ)
    (hLeftNonneg : ∀ A : ι → G, 0 ≤ left A)
    (hRightNonneg : ∀ A : ι → G, 0 ≤ right A)
    (A B : ι → G)
    (target : ι)
    (leftRatio rightRatio : ℝ)
    (hLeftRatio : 0 ≤ leftRatio)
    (hRightRatio : 0 ≤ rightRatio)
    (hLeftCross :
      FinitePositiveWeightSingleSiteCrossRatioBound
        left A B target leftRatio)
    (hRightCross :
      FinitePositiveWeightSingleSiteCrossRatioBound
        right A B target rightRatio) :
    FinitePositiveWeightSingleSiteCrossRatioBound
      (finitePositiveWeightProduct left right)
      A B target (leftRatio * rightRatio) := by
  intro g h
  have hLeft := hLeftCross g h
  have hRight := hRightCross g h
  calc
    finitePositiveWeightProduct left right
          (Function.update A target g) *
        finitePositiveWeightProduct left right
          (Function.update B target h) =
      (left (Function.update A target g) *
          left (Function.update B target h)) *
        (right (Function.update A target g) *
          right (Function.update B target h)) := by
      unfold finitePositiveWeightProduct
      ring
    _ ≤
      (leftRatio *
          (left (Function.update B target g) *
            left (Function.update A target h))) *
        (rightRatio *
          (right (Function.update B target g) *
            right (Function.update A target h))) := by
      exact mul_le_mul hLeft hRight
        (mul_nonneg
          (hRightNonneg (Function.update A target g))
          (hRightNonneg (Function.update B target h)))
        (mul_nonneg hLeftRatio
          (mul_nonneg
            (hLeftNonneg (Function.update B target g))
            (hLeftNonneg (Function.update A target h))))
    _ =
      (leftRatio * rightRatio) *
        (finitePositiveWeightProduct left right
            (Function.update B target g) *
          finitePositiveWeightProduct left right
            (Function.update A target h)) := by
      unfold finitePositiveWeightProduct
      ring

/-- If the second factor is target-fiber independent, a cross-ratio bound for
the first factor transfers unchanged to the product weight. -/
theorem finitePositiveWeightProduct_singleSiteCrossRatioBound_of_rightIndependent
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    (left right : (ι → G) → ℝ)
    (hLeftNonneg : ∀ A : ι → G, 0 ≤ left A)
    (hRightNonneg : ∀ A : ι → G, 0 ≤ right A)
    (A B : ι → G)
    (target : ι)
    (ratio : ℝ)
    (hRatio : 0 ≤ ratio)
    (hLeftCross :
      FinitePositiveWeightSingleSiteCrossRatioBound
        left A B target ratio)
    (hRightIndependent :
      FiniteProductFunctionIndependentOfCoordinate right target) :
    FinitePositiveWeightSingleSiteCrossRatioBound
      (finitePositiveWeightProduct left right)
      A B target ratio := by
  have hProduct :=
    finitePositiveWeightProduct_singleSiteCrossRatioBound
      left right hLeftNonneg hRightNonneg A B target ratio 1
      hRatio (by norm_num) hLeftCross
      (finiteProductFunctionIndependentOfCoordinate_crossRatio_one
        right A B target hRightIndependent)
  simpa using hProduct

end

end MathlibAnalytic
end MGAP4D
