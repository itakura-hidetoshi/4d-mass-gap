import MGAP4D.MathlibAnalytic.FiniteStrictProbabilityL2MeasurePreservingPullback
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

namespace FiniteStrictProbabilityMap

variable
    {X Y : Type}
    [Fintype X]
    [Fintype Y]
    {P : FiniteStrictProbabilityL2Data X}
    {Q : FiniteStrictProbabilityL2Data Y}

/-- Weighted numerator of finite conditional expectation over one fibre.  The
noncomputable wrapper hides the equality decision on the target type from the
public theorem surface. -/
noncomputable def conditionalFiberWeightedSum
    (M : FiniteStrictProbabilityMap X Y P Q)
    (f : X → ℝ)
    (y : Y) : ℝ := by
  classical
  exact ∑ x : X,
    if M.toFun x = y then P.weight x * f x else 0

/-- Probability-weighted conditional expectation of a source observable along
an exact finite probability map.  The target value is the conditional weighted
average over one fibre. -/
noncomputable def observableConditionalExpectationLinearMap
    (M : FiniteStrictProbabilityMap X Y P Q) :
    (X → ℝ) →ₗ[ℝ] (Y → ℝ) := by
  classical
  exact
    { toFun := fun f y =>
        M.conditionalFiberWeightedSum f y / Q.weight y
      map_add' := by
        intro f g
        funext y
        change
          M.conditionalFiberWeightedSum (f + g) y / Q.weight y =
            M.conditionalFiberWeightedSum f y / Q.weight y +
              M.conditionalFiberWeightedSum g y / Q.weight y
        unfold conditionalFiberWeightedSum
        rw [← add_div]
        congr 1
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _hx
        by_cases hxy : M.toFun x = y
        · simp [hxy, mul_add]
        · simp [hxy]
      map_smul' := by
        intro c f
        funext y
        change
          M.conditionalFiberWeightedSum (c • f) y / Q.weight y =
            c * (M.conditionalFiberWeightedSum f y / Q.weight y)
        unfold conditionalFiberWeightedSum
        rw [← mul_div_assoc]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _hx
        by_cases hxy : M.toFun x = y
        · simp [hxy]
          ring
        · simp [hxy] }

@[simp] theorem observableConditionalExpectationLinearMap_apply
    (M : FiniteStrictProbabilityMap X Y P Q)
    (f : X → ℝ)
    (y : Y) :
    M.observableConditionalExpectationLinearMap f y =
      M.conditionalFiberWeightedSum f y / Q.weight y :=
  rfl

/-- Conditional expectation is a left inverse of pullback on observables. -/
theorem observableConditionalExpectation_observablePullback
    (M : FiniteStrictProbabilityMap X Y P Q)
    (f : Y → ℝ) :
    M.observableConditionalExpectationLinearMap
        (M.observablePullbackLinearMap f) = f := by
  classical
  funext y
  rw [M.observableConditionalExpectationLinearMap_apply]
  unfold conditionalFiberWeightedSum
  change
    (∑ x : X,
      if M.toFun x = y then P.weight x * f (M.toFun x) else 0) /
        Q.weight y = f y
  have hpush := M.weight_pushforward y
  unfold finiteProbabilityPushforwardWeight at hpush
  have hsum :
      (∑ x : X,
        if M.toFun x = y then P.weight x * f (M.toFun x) else 0) =
        Q.weight y * f y := by
    calc
      (∑ x : X,
        if M.toFun x = y then P.weight x * f (M.toFun x) else 0) =
        ∑ x : X,
          (if M.toFun x = y then P.weight x else 0) * f y := by
            apply Finset.sum_congr rfl
            intro x _hx
            by_cases hxy : M.toFun x = y
            · simp [hxy]
            · simp [hxy]
      _ =
        (∑ x : X, if M.toFun x = y then P.weight x else 0) * f y := by
          rw [Finset.sum_mul]
      _ = Q.weight y * f y := by rw [hpush]
  rw [hsum]
  field_simp [ne_of_gt (Q.weight_pos y)]

/-- `L²` conditional expectation in square-root-density coordinates.  It is
the Hilbert-space map covariant with the geometric probability map, opposite
to the contravariant pullback. -/
noncomputable def l2ConditionalExpectationLinearMap
    (M : FiniteStrictProbabilityMap X Y P Q) :
    FiniteProbabilityL2Carrier X →ₗ[ℝ]
      FiniteProbabilityL2Carrier Y :=
  Q.observableEmbedLinearMap.comp
    (M.observableConditionalExpectationLinearMap.comp
      P.coordinateObserveLinearMap)

/-- Conditional expectation is an exact left inverse of the probability `L²`
pullback. -/
theorem l2ConditionalExpectation_l2Pullback
    (M : FiniteStrictProbabilityMap X Y P Q)
    (y : FiniteProbabilityL2Carrier Y) :
    M.l2ConditionalExpectationLinearMap
        (M.l2PullbackLinearMap y) = y := by
  change
    Q.observableEmbedLinearMap
      (M.observableConditionalExpectationLinearMap
        (P.coordinateObserveLinearMap
          (P.observableEmbedLinearMap
            (M.observablePullbackLinearMap
              (Q.coordinateObserveLinearMap y))))) = y
  rw [P.coordinateObserve_observableEmbed]
  rw [M.observableConditionalExpectation_observablePullback]
  exact Q.observableEmbed_coordinateObserve y

/-- Exact Hilbert-adjoint pairing: conditional expectation is the adjoint of
measure-preserving `L²` pullback. -/
theorem l2ConditionalExpectation_adjoint_pairing
    (M : FiniteStrictProbabilityMap X Y P Q)
    (x : FiniteProbabilityL2Carrier X)
    (y : FiniteProbabilityL2Carrier Y) :
    inner ℝ (M.l2ConditionalExpectationLinearMap x) y =
      inner ℝ x (M.l2PullbackLinearMap y) := by
  classical
  let g : X → ℝ := P.coordinateObserveLinearMap x
  let f : Y → ℝ := Q.coordinateObserveLinearMap y
  have hx : P.observableEmbedLinearMap g = x :=
    P.observableEmbed_coordinateObserve x
  have hy : Q.observableEmbedLinearMap f = y :=
    Q.observableEmbed_coordinateObserve y
  rw [← hx, ← hy]
  change
    inner ℝ
        (Q.observableEmbedLinearMap
          (M.observableConditionalExpectationLinearMap
            (P.coordinateObserveLinearMap
              (P.observableEmbedLinearMap g))))
        (Q.observableEmbedLinearMap f) =
      inner ℝ
        (P.observableEmbedLinearMap g)
        (P.observableEmbedLinearMap
          (M.observablePullbackLinearMap
            (Q.coordinateObserveLinearMap
              (Q.observableEmbedLinearMap f))))
  rw [P.coordinateObserve_observableEmbed, Q.coordinateObserve_observableEmbed]
  rw [Q.inner_observableEmbed, P.inner_observableEmbed]
  change
    (∑ z : Y,
      Q.weight z *
        M.observableConditionalExpectationLinearMap g z * f z) =
      ∑ a : X, P.weight a * g a * f (M.toFun a)
  calc
    (∑ z : Y,
      Q.weight z *
        M.observableConditionalExpectationLinearMap g z * f z) =
      ∑ z : Y, M.conditionalFiberWeightedSum g z * f z := by
        apply Finset.sum_congr rfl
        intro z _hz
        rw [M.observableConditionalExpectationLinearMap_apply]
        field_simp [ne_of_gt (Q.weight_pos z)] <;> ring
    _ = ∑ z : Y, ∑ a : X,
        if M.toFun a = z then P.weight a * g a * f z else 0 := by
          apply Finset.sum_congr rfl
          intro z _hz
          unfold conditionalFiberWeightedSum
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro a _ha
          by_cases haz : M.toFun a = z
          · simp [haz]
          · simp [haz]
    _ = ∑ a : X, ∑ z : Y,
        if M.toFun a = z then P.weight a * g a * f z else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ a : X, P.weight a * g a * f (M.toFun a) := by
          apply Finset.sum_congr rfl
          intro a _ha
          simp

/-- The same adjoint identity in pullback-first orientation. -/
theorem l2Pullback_adjoint_pairing
    (M : FiniteStrictProbabilityMap X Y P Q)
    (y : FiniteProbabilityL2Carrier Y)
    (x : FiniteProbabilityL2Carrier X) :
    inner ℝ (M.l2PullbackLinearMap y) x =
      inner ℝ y (M.l2ConditionalExpectationLinearMap x) := by
  calc
    inner ℝ (M.l2PullbackLinearMap y) x =
        inner ℝ x (M.l2PullbackLinearMap y) := real_inner_comm _ _
    _ = inner ℝ (M.l2ConditionalExpectationLinearMap x) y :=
      (M.l2ConditionalExpectation_adjoint_pairing x y).symm
    _ = inner ℝ y (M.l2ConditionalExpectationLinearMap x) :=
      real_inner_comm _ _

/-- Orthogonal projection onto the subspace of source vectors measurable with
respect to the coarse probability map. -/
noncomputable def l2CoarseProjectionLinearMap
    (M : FiniteStrictProbabilityMap X Y P Q) :
    FiniteProbabilityL2Carrier X →ₗ[ℝ]
      FiniteProbabilityL2Carrier X :=
  M.l2PullbackLinearMap.comp M.l2ConditionalExpectationLinearMap

/-- The coarse-measurable projection is idempotent. -/
theorem l2CoarseProjection_idempotent
    (M : FiniteStrictProbabilityMap X Y P Q)
    (x : FiniteProbabilityL2Carrier X) :
    M.l2CoarseProjectionLinearMap
        (M.l2CoarseProjectionLinearMap x) =
      M.l2CoarseProjectionLinearMap x := by
  change
    M.l2PullbackLinearMap
        (M.l2ConditionalExpectationLinearMap
          (M.l2PullbackLinearMap
            (M.l2ConditionalExpectationLinearMap x))) =
      M.l2PullbackLinearMap
        (M.l2ConditionalExpectationLinearMap x)
  rw [M.l2ConditionalExpectation_l2Pullback]

/-- Every pulled-back coarse vector is fixed by the coarse-measurable
projection. -/
theorem l2CoarseProjection_l2Pullback
    (M : FiniteStrictProbabilityMap X Y P Q)
    (y : FiniteProbabilityL2Carrier Y) :
    M.l2CoarseProjectionLinearMap (M.l2PullbackLinearMap y) =
      M.l2PullbackLinearMap y := by
  change
    M.l2PullbackLinearMap
        (M.l2ConditionalExpectationLinearMap
          (M.l2PullbackLinearMap y)) =
      M.l2PullbackLinearMap y
  rw [M.l2ConditionalExpectation_l2Pullback]

/-- The coarse-measurable projection is symmetric, hence the orthogonal
projection associated with conditional expectation and pullback. -/
theorem l2CoarseProjection_isSymmetric
    (M : FiniteStrictProbabilityMap X Y P Q) :
    M.l2CoarseProjectionLinearMap.IsSymmetric := by
  intro x z
  calc
    inner ℝ (M.l2CoarseProjectionLinearMap x) z =
        inner ℝ
          (M.l2PullbackLinearMap
            (M.l2ConditionalExpectationLinearMap x)) z := rfl
    _ = inner ℝ
        (M.l2ConditionalExpectationLinearMap x)
        (M.l2ConditionalExpectationLinearMap z) :=
      M.l2Pullback_adjoint_pairing
        (M.l2ConditionalExpectationLinearMap x) z
    _ = inner ℝ x
        (M.l2PullbackLinearMap
          (M.l2ConditionalExpectationLinearMap z)) :=
      M.l2ConditionalExpectation_adjoint_pairing x
        (M.l2ConditionalExpectationLinearMap z)
    _ = inner ℝ x (M.l2CoarseProjectionLinearMap z) := rfl

/-- Compress a source continuous linear operator to the target probability
`L²` space by conditional expectation after source evolution of the pulled-back
coarse vector.  This is the exact finite-probability operator compression
`E A U`. -/
noncomputable def compressContinuousLinearOperator
    (M : FiniteStrictProbabilityMap X Y P Q)
    (A : FiniteProbabilityL2Carrier X →L[ℝ]
      FiniteProbabilityL2Carrier X) :
    FiniteProbabilityL2Carrier Y →L[ℝ]
      FiniteProbabilityL2Carrier Y :=
  LinearMap.toContinuousLinearMap
    (M.l2ConditionalExpectationLinearMap.comp
      (A.toLinearMap.comp M.l2PullbackLinearMap))

@[simp] theorem compressContinuousLinearOperator_apply
    (M : FiniteStrictProbabilityMap X Y P Q)
    (A : FiniteProbabilityL2Carrier X →L[ℝ]
      FiniteProbabilityL2Carrier X)
    (y : FiniteProbabilityL2Carrier Y) :
    M.compressContinuousLinearOperator A y =
      M.l2ConditionalExpectationLinearMap
        (A (M.l2PullbackLinearMap y)) :=
  rfl

/-- Compression preserves symmetry because conditional expectation is exactly
the Hilbert adjoint of pullback. -/
theorem compressContinuousLinearOperator_isSymmetric
    (M : FiniteStrictProbabilityMap X Y P Q)
    (A : FiniteProbabilityL2Carrier X →L[ℝ]
      FiniteProbabilityL2Carrier X)
    (hA : A.toLinearMap.IsSymmetric) :
    (M.compressContinuousLinearOperator A).toLinearMap.IsSymmetric := by
  intro y z
  change
    inner ℝ
        (M.l2ConditionalExpectationLinearMap
          (A (M.l2PullbackLinearMap y))) z =
      inner ℝ y
        (M.l2ConditionalExpectationLinearMap
          (A (M.l2PullbackLinearMap z)))
  calc
    inner ℝ
        (M.l2ConditionalExpectationLinearMap
          (A (M.l2PullbackLinearMap y))) z =
      inner ℝ
        (A (M.l2PullbackLinearMap y))
        (M.l2PullbackLinearMap z) :=
          M.l2ConditionalExpectation_adjoint_pairing _ _
    _ = inner ℝ
        (M.l2PullbackLinearMap y)
        (A (M.l2PullbackLinearMap z)) :=
          hA _ _
    _ = inner ℝ y
        (M.l2ConditionalExpectationLinearMap
          (A (M.l2PullbackLinearMap z))) :=
          M.l2Pullback_adjoint_pairing _ _

/-- Every quadratic lower bound on the source operator survives exactly under
finite-probability compression. -/
theorem compressContinuousLinearOperator_quadratic_lower_bound
    (M : FiniteStrictProbabilityMap X Y P Q)
    (A : FiniteProbabilityL2Carrier X →L[ℝ]
      FiniteProbabilityL2Carrier X)
    (c : ℝ)
    (hA : ∀ x : FiniteProbabilityL2Carrier X,
      c * ‖x‖ ^ 2 ≤ inner ℝ (A x) x)
    (y : FiniteProbabilityL2Carrier Y) :
    c * ‖y‖ ^ 2 ≤
      inner ℝ (M.compressContinuousLinearOperator A y) y := by
  calc
    c * ‖y‖ ^ 2 =
        c * ‖M.l2PullbackLinearMap y‖ ^ 2 := by
          rw [M.norm_sq_l2PullbackLinearMap]
    _ ≤ inner ℝ
        (A (M.l2PullbackLinearMap y))
        (M.l2PullbackLinearMap y) :=
      hA (M.l2PullbackLinearMap y)
    _ = inner ℝ (M.compressContinuousLinearOperator A y) y := by
      symm
      exact M.l2ConditionalExpectation_adjoint_pairing _ _

/-- Strong cross-volume intertwining residual.  It vanishes exactly when the
source operator preserves pulled-back coarse vectors and agrees there with the
target operator. -/
noncomputable def intertwiningResidualLinearMap
    (M : FiniteStrictProbabilityMap X Y P Q)
    (A : FiniteProbabilityL2Carrier X →L[ℝ]
      FiniteProbabilityL2Carrier X)
    (B : FiniteProbabilityL2Carrier Y →L[ℝ]
      FiniteProbabilityL2Carrier Y) :
    FiniteProbabilityL2Carrier Y →ₗ[ℝ]
      FiniteProbabilityL2Carrier X :=
  (A.toLinearMap.comp M.l2PullbackLinearMap) -
    (M.l2PullbackLinearMap.comp B.toLinearMap)

/-- Vanishing of the residual is precisely exact operator intertwining. -/
theorem intertwiningResidualLinearMap_eq_zero_iff
    (M : FiniteStrictProbabilityMap X Y P Q)
    (A : FiniteProbabilityL2Carrier X →L[ℝ]
      FiniteProbabilityL2Carrier X)
    (B : FiniteProbabilityL2Carrier Y →L[ℝ]
      FiniteProbabilityL2Carrier Y) :
    M.intertwiningResidualLinearMap A B = 0 ↔
      ∀ y : FiniteProbabilityL2Carrier Y,
        A (M.l2PullbackLinearMap y) =
          M.l2PullbackLinearMap (B y) := by
  constructor
  · intro h y
    have hy := LinearMap.congr_fun h y
    change
      A (M.l2PullbackLinearMap y) -
          M.l2PullbackLinearMap (B y) = 0 at hy
    exact sub_eq_zero.mp hy
  · intro h
    apply LinearMap.ext
    intro y
    change
      A (M.l2PullbackLinearMap y) -
          M.l2PullbackLinearMap (B y) = 0
    exact sub_eq_zero.mpr (h y)

/-- Exact intertwining implies that the target operator is the compression of
the source operator.  The converse is intentionally not asserted: compression
equality alone does not force invariance of the pulled-back coarse subspace. -/
theorem compressContinuousLinearOperator_eq_of_intertwining
    (M : FiniteStrictProbabilityMap X Y P Q)
    (A : FiniteProbabilityL2Carrier X →L[ℝ]
      FiniteProbabilityL2Carrier X)
    (B : FiniteProbabilityL2Carrier Y →L[ℝ]
      FiniteProbabilityL2Carrier Y)
    (h : ∀ y : FiniteProbabilityL2Carrier Y,
      A (M.l2PullbackLinearMap y) =
        M.l2PullbackLinearMap (B y)) :
    M.compressContinuousLinearOperator A = B := by
  apply ContinuousLinearMap.ext
  intro y
  rw [M.compressContinuousLinearOperator_apply, h y]
  exact M.l2ConditionalExpectation_l2Pullback (B y)

/-- Audit-visible generic finite-probability compression package. -/
structure ConditionalExpectationCompressionPackage
    (M : FiniteStrictProbabilityMap X Y P Q) where
  conditionalExpectation :
    FiniteProbabilityL2Carrier X →ₗ[ℝ]
      FiniteProbabilityL2Carrier Y
  conditionalExpectation_eq :
    conditionalExpectation = M.l2ConditionalExpectationLinearMap
  leftInverse :
    ∀ y : FiniteProbabilityL2Carrier Y,
      conditionalExpectation (M.l2PullbackLinearMap y) = y
  projection :
    FiniteProbabilityL2Carrier X →ₗ[ℝ]
      FiniteProbabilityL2Carrier X
  projection_eq : projection = M.l2CoarseProjectionLinearMap
  projectionIdempotent : ∀ x,
    projection (projection x) = projection x
  projectionSymmetric : projection.IsSymmetric
  adjointPairing : ∀ x y,
    inner ℝ (conditionalExpectation x) y =
      inner ℝ x (M.l2PullbackLinearMap y)

/-- Construct the complete generic conditional-expectation/compression receipt
attached to one exact finite probability map. -/
noncomputable def conditionalExpectationCompressionPackage
    (M : FiniteStrictProbabilityMap X Y P Q) :
    ConditionalExpectationCompressionPackage M where
  conditionalExpectation := M.l2ConditionalExpectationLinearMap
  conditionalExpectation_eq := rfl
  leftInverse := M.l2ConditionalExpectation_l2Pullback
  projection := M.l2CoarseProjectionLinearMap
  projection_eq := rfl
  projectionIdempotent := M.l2CoarseProjection_idempotent
  projectionSymmetric := M.l2CoarseProjection_isSymmetric
  adjointPairing := M.l2ConditionalExpectation_adjoint_pairing

end FiniteStrictProbabilityMap

end

end MathlibAnalytic
end MGAP4D
