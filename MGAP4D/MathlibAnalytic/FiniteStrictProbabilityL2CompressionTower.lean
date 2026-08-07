import MGAP4D.MathlibAnalytic.FiniteStrictProbabilityL2ConditionalExpectationCompression
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

namespace FiniteStrictProbabilityMap

variable
    {X Y Z : Type}
    [Fintype X]
    [Fintype Y]
    [Fintype Z]
    {P : FiniteStrictProbabilityL2Data X}
    {Q : FiniteStrictProbabilityL2Data Y}
    {R : FiniteStrictProbabilityL2Data Z}

/-- Conditional expectation is covariantly functorial under composition of
exact finite probability maps.  This is the finite tower property on
observables. -/
theorem observableConditionalExpectation_comp
    (M : FiniteStrictProbabilityMap X Y P Q)
    (N : FiniteStrictProbabilityMap Y Z Q R)
    (f : X → ℝ) :
    N.observableConditionalExpectationLinearMap
        (M.observableConditionalExpectationLinearMap f) =
      (M.comp N).observableConditionalExpectationLinearMap f := by
  classical
  funext z
  rw [N.observableConditionalExpectationLinearMap_apply]
  rw [(M.comp N).observableConditionalExpectationLinearMap_apply]
  unfold conditionalFiberWeightedSum
  change
    (∑ y : Y,
      if N.toFun y = z then
        Q.weight y *
          (M.conditionalFiberWeightedSum f y / Q.weight y)
      else 0) / R.weight z =
      (∑ x : X,
        if N.toFun (M.toFun x) = z then P.weight x * f x else 0) /
          R.weight z
  congr 1
  calc
    (∑ y : Y,
      if N.toFun y = z then
        Q.weight y *
          (M.conditionalFiberWeightedSum f y / Q.weight y)
      else 0) =
      ∑ y : Y,
        if N.toFun y = z then M.conditionalFiberWeightedSum f y else 0 := by
          apply Finset.sum_congr rfl
          intro y _hy
          by_cases hyz : N.toFun y = z
          · rw [if_pos hyz, if_pos hyz]
            field_simp [ne_of_gt (Q.weight_pos y)]
          · simp [hyz]
    _ = ∑ y : Y, ∑ x : X,
        if N.toFun y = z then
          if M.toFun x = y then P.weight x * f x else 0
        else 0 := by
          apply Finset.sum_congr rfl
          intro y _hy
          unfold conditionalFiberWeightedSum
          by_cases hyz : N.toFun y = z
          · simp only [hyz, if_pos]
          · simp only [hyz, if_neg, Finset.sum_const_zero]
    _ = ∑ x : X, ∑ y : Y,
        if N.toFun y = z then
          if M.toFun x = y then P.weight x * f x else 0
        else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ x : X,
        if N.toFun (M.toFun x) = z then P.weight x * f x else 0 := by
          apply Finset.sum_congr rfl
          intro x _hx
          by_cases hxz : N.toFun (M.toFun x) = z
          · rw [if_pos hxz]
            rw [Fintype.sum_eq_single (M.toFun x)]
            · simp [hxz]
            · intro y hyne
              by_cases hyz : N.toFun y = z
              · rw [if_pos hyz, if_neg (Ne.symm hyne)]
              · rw [if_neg hyz]
          · rw [if_neg hxz]
            apply Fintype.sum_eq_zero
            intro y
            by_cases hyz : N.toFun y = z
            · rw [if_pos hyz]
              have hxy : M.toFun x ≠ y := by
                intro hxy
                subst y
                exact hxz hyz
              rw [if_neg hxy]
            · rw [if_neg hyz]

/-- Covariant tower property on square-root-density `L²`: conditioning from
`X` to `Y` and then from `Y` to `Z` is exactly conditioning along the composed
probability map. -/
theorem l2ConditionalExpectationLinearMap_comp
    (M : FiniteStrictProbabilityMap X Y P Q)
    (N : FiniteStrictProbabilityMap Y Z Q R)
    (x : FiniteProbabilityL2Carrier X) :
    N.l2ConditionalExpectationLinearMap
        (M.l2ConditionalExpectationLinearMap x) =
      (M.comp N).l2ConditionalExpectationLinearMap x := by
  change
    R.observableEmbedLinearMap
      (N.observableConditionalExpectationLinearMap
        (Q.coordinateObserveLinearMap
          (Q.observableEmbedLinearMap
            (M.observableConditionalExpectationLinearMap
              (P.coordinateObserveLinearMap x))))) =
      R.observableEmbedLinearMap
        ((M.comp N).observableConditionalExpectationLinearMap
          (P.coordinateObserveLinearMap x))
  rw [Q.coordinateObserve_observableEmbed]
  rw [M.observableConditionalExpectation_comp N]

/-- The conditional expectation attached to a two-stage probability map is the
covariant composite of the two one-stage conditional expectations. -/
theorem l2ConditionalExpectationLinearMap_comp_map
    (M : FiniteStrictProbabilityMap X Y P Q)
    (N : FiniteStrictProbabilityMap Y Z Q R) :
    (M.comp N).l2ConditionalExpectationLinearMap =
      N.l2ConditionalExpectationLinearMap.comp
        M.l2ConditionalExpectationLinearMap := by
  apply LinearMap.ext
  intro x
  exact (M.l2ConditionalExpectationLinearMap_comp N x).symm

/-- The coarse projection for a composed probability map is obtained by
conditioning to the intermediate scale, applying the intermediate coarse
projection, and pulling back to the original source scale. -/
theorem l2CoarseProjection_comp_apply
    (M : FiniteStrictProbabilityMap X Y P Q)
    (N : FiniteStrictProbabilityMap Y Z Q R)
    (x : FiniteProbabilityL2Carrier X) :
    (M.comp N).l2CoarseProjectionLinearMap x =
      M.l2PullbackLinearMap
        (N.l2CoarseProjectionLinearMap
          (M.l2ConditionalExpectationLinearMap x)) := by
  change
    (M.comp N).l2PullbackLinearMap
        ((M.comp N).l2ConditionalExpectationLinearMap x) =
      M.l2PullbackLinearMap
        (N.l2PullbackLinearMap
          (N.l2ConditionalExpectationLinearMap
            (M.l2ConditionalExpectationLinearMap x)))
  rw [← M.l2ConditionalExpectationLinearMap_comp N x]
  symm
  exact M.l2PullbackLinearMap_comp N
    (N.l2ConditionalExpectationLinearMap
      (M.l2ConditionalExpectationLinearMap x))

/-- The composed coarse projection fixes every vector pulled back from the
coarsest target scale. -/
theorem l2CoarseProjection_comp_l2Pullback
    (M : FiniteStrictProbabilityMap X Y P Q)
    (N : FiniteStrictProbabilityMap Y Z Q R)
    (z : FiniteProbabilityL2Carrier Z) :
    (M.comp N).l2CoarseProjectionLinearMap
        ((M.comp N).l2PullbackLinearMap z) =
      (M.comp N).l2PullbackLinearMap z :=
  (M.comp N).l2CoarseProjection_l2Pullback z

/-- Operator compression is associative along a tower of exact finite
probability maps.  Compressing `A` from `X` to `Y` and then from `Y` to `Z`
is exactly the same operator as direct compression along `X → Z`. -/
theorem compressContinuousLinearOperator_comp
    (M : FiniteStrictProbabilityMap X Y P Q)
    (N : FiniteStrictProbabilityMap Y Z Q R)
    (A : FiniteProbabilityL2Carrier X →L[ℝ]
      FiniteProbabilityL2Carrier X) :
    (M.comp N).compressContinuousLinearOperator A =
      N.compressContinuousLinearOperator
        (M.compressContinuousLinearOperator A) := by
  apply ContinuousLinearMap.ext
  intro z
  rw [(M.comp N).compressContinuousLinearOperator_apply]
  rw [N.compressContinuousLinearOperator_apply]
  rw [M.compressContinuousLinearOperator_apply]
  rw [← M.l2ConditionalExpectationLinearMap_comp N]
  rw [M.l2PullbackLinearMap_comp N]

/-- A quadratic lower bound may be transported through an arbitrary two-stage
compression either directly or sequentially, with exactly the same constant. -/
theorem compressContinuousLinearOperator_comp_quadratic_lower_bound
    (M : FiniteStrictProbabilityMap X Y P Q)
    (N : FiniteStrictProbabilityMap Y Z Q R)
    (A : FiniteProbabilityL2Carrier X →L[ℝ]
      FiniteProbabilityL2Carrier X)
    (c : ℝ)
    (hA : ∀ x : FiniteProbabilityL2Carrier X,
      c * ‖x‖ ^ 2 ≤ inner ℝ (A x) x)
    (z : FiniteProbabilityL2Carrier Z) :
    c * ‖z‖ ^ 2 ≤
      inner ℝ
        ((N.compressContinuousLinearOperator
          (M.compressContinuousLinearOperator A)) z) z := by
  rw [← M.compressContinuousLinearOperator_comp N A]
  exact
    (M.comp N).compressContinuousLinearOperator_quadratic_lower_bound
      A c hA z

/-- Symmetry likewise survives direct or sequential two-stage compression. -/
theorem compressContinuousLinearOperator_comp_isSymmetric
    (M : FiniteStrictProbabilityMap X Y P Q)
    (N : FiniteStrictProbabilityMap Y Z Q R)
    (A : FiniteProbabilityL2Carrier X →L[ℝ]
      FiniteProbabilityL2Carrier X)
    (hA : A.toLinearMap.IsSymmetric) :
    (N.compressContinuousLinearOperator
      (M.compressContinuousLinearOperator A)).toLinearMap.IsSymmetric := by
  rw [← M.compressContinuousLinearOperator_comp N A]
  exact
    (M.comp N).compressContinuousLinearOperator_isSymmetric A hA

/-- Audit-visible generic tower package for conditional expectation, pullback,
coarse projection and operator compression. -/
structure CompressionTowerPackage
    (M : FiniteStrictProbabilityMap X Y P Q)
    (N : FiniteStrictProbabilityMap Y Z Q R) where
  conditionalTower : ∀ x,
    N.l2ConditionalExpectationLinearMap
        (M.l2ConditionalExpectationLinearMap x) =
      (M.comp N).l2ConditionalExpectationLinearMap x
  pullbackCocycle : ∀ z,
    M.l2PullbackLinearMap (N.l2PullbackLinearMap z) =
      (M.comp N).l2PullbackLinearMap z
  projectionTower : ∀ x,
    (M.comp N).l2CoarseProjectionLinearMap x =
      M.l2PullbackLinearMap
        (N.l2CoarseProjectionLinearMap
          (M.l2ConditionalExpectationLinearMap x))
  compressionAssociative : ∀ A,
    (M.comp N).compressContinuousLinearOperator A =
      N.compressContinuousLinearOperator
        (M.compressContinuousLinearOperator A)

/-- Construct the complete generic two-stage compression tower receipt. -/
noncomputable def compressionTowerPackage
    (M : FiniteStrictProbabilityMap X Y P Q)
    (N : FiniteStrictProbabilityMap Y Z Q R) :
    CompressionTowerPackage M N where
  conditionalTower := M.l2ConditionalExpectationLinearMap_comp N
  pullbackCocycle := M.l2PullbackLinearMap_comp N
  projectionTower := M.l2CoarseProjection_comp_apply N
  compressionAssociative := M.compressContinuousLinearOperator_comp N

end FiniteStrictProbabilityMap

end

end MathlibAnalytic
end MGAP4D
