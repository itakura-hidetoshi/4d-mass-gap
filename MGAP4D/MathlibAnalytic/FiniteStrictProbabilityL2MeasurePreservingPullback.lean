import MGAP4D.MathlibAnalytic.FiniteStrictProbabilityL2OrthonormalCoordinates
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

/-- Pushforward weight of one target point under a map from a finite weighted
space.  The definition is noncomputable only to hide the equality decision on
the target type. -/
noncomputable def finiteProbabilityPushforwardWeight
    {X Y : Type}
    [Fintype X]
    (P : FiniteStrictProbabilityL2Data X)
    (f : X → Y)
    (y : Y) : ℝ := by
  classical
  exact ∑ x : X, if f x = y then P.weight x else 0

/-- A map between strict finite probability spaces with exact pushforward
weights.  This is the finite discrete form of a measure-preserving map. -/
structure FiniteStrictProbabilityMap
    (X Y : Type)
    [Fintype X]
    [Fintype Y]
    (P : FiniteStrictProbabilityL2Data X)
    (Q : FiniteStrictProbabilityL2Data Y) where
  toFun : X → Y
  weight_pushforward :
    ∀ y : Y,
      finiteProbabilityPushforwardWeight P toFun y = Q.weight y

namespace FiniteStrictProbabilityMap

variable
    {X Y Z : Type}
    [Fintype X]
    [Fintype Y]
    [Fintype Z]
    {P : FiniteStrictProbabilityL2Data X}
    {Q : FiniteStrictProbabilityL2Data Y}
    {R : FiniteStrictProbabilityL2Data Z}

/-- Pull an observable on the target finite probability space back along a
measure-preserving finite map. -/
def observablePullbackLinearMap
    (M : FiniteStrictProbabilityMap X Y P Q) :
    (Y → ℝ) →ₗ[ℝ] (X → ℝ) where
  toFun f := fun x => f (M.toFun x)
  map_add' f g := by
    funext x
    rfl
  map_smul' c f := by
    funext x
    rfl

@[simp] theorem observablePullbackLinearMap_apply
    (M : FiniteStrictProbabilityMap X Y P Q)
    (f : Y → ℝ)
    (x : X) :
    M.observablePullbackLinearMap f x = f (M.toFun x) :=
  rfl

/-- Exact weighted change-of-variables formula for a strict finite probability
map. -/
theorem weighted_sum_comp
    (M : FiniteStrictProbabilityMap X Y P Q)
    (f : Y → ℝ) :
    ∑ x : X, P.weight x * f (M.toFun x) =
      ∑ y : Y, Q.weight y * f y := by
  classical
  calc
    ∑ x : X, P.weight x * f (M.toFun x) =
        ∑ x : X, ∑ y : Y,
          if M.toFun x = y then P.weight x * f y else 0 := by
      apply Finset.sum_congr rfl
      intro x _hx
      simp
    _ = ∑ y : Y, ∑ x : X,
          if M.toFun x = y then P.weight x * f y else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ y : Y,
          finiteProbabilityPushforwardWeight P M.toFun y * f y := by
      apply Finset.sum_congr rfl
      intro y _hy
      unfold finiteProbabilityPushforwardWeight
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases hxy : M.toFun x = y
      · simp [hxy]
      · simp [hxy]
    _ = ∑ y : Y, Q.weight y * f y := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [M.weight_pushforward y]

/-- Coordinate realization of the measure-preserving pullback.  It decodes a
target square-root-density vector to its observable, pulls the observable back,
and re-embeds it with the source probability weights. -/
noncomputable def l2PullbackLinearMap
    (M : FiniteStrictProbabilityMap X Y P Q) :
    FiniteProbabilityL2Carrier Y →ₗ[ℝ] FiniteProbabilityL2Carrier X :=
  P.observableEmbedLinearMap.comp
    (M.observablePullbackLinearMap.comp Q.coordinateObserveLinearMap)

@[simp] theorem l2PullbackLinearMap_apply
    (M : FiniteStrictProbabilityMap X Y P Q)
    (y : FiniteProbabilityL2Carrier Y)
    (x : X) :
    M.l2PullbackLinearMap y x =
      Real.sqrt (P.weight x) *
        (y (M.toFun x) / Real.sqrt (Q.weight (M.toFun x))) :=
  rfl

/-- Exact preservation of squared norm by finite measure-preserving pullback. -/
theorem norm_sq_l2PullbackLinearMap
    (M : FiniteStrictProbabilityMap X Y P Q)
    (y : FiniteProbabilityL2Carrier Y) :
    ‖M.l2PullbackLinearMap y‖ ^ 2 = ‖y‖ ^ 2 := by
  let f : Y → ℝ := Q.coordinateObserveLinearMap y
  have hpull :
      M.l2PullbackLinearMap y =
        P.observableEmbedLinearMap (M.observablePullbackLinearMap f) := rfl
  rw [hpull, P.norm_sq_observableEmbed]
  change
    (∑ x : X, P.weight x * (f (M.toFun x)) ^ 2) = ‖y‖ ^ 2
  rw [M.weighted_sum_comp (fun z => (f z) ^ 2)]
  rw [← Q.norm_sq_observableEmbed f]
  rw [show Q.observableEmbedLinearMap f = y by
    exact Q.observableEmbed_coordinateObserve y]

/-- A finite measure-preserving map induces a canonical real-linear isometry
between square-root-density `L²` carriers by pullback. -/
noncomputable def l2PullbackLinearIsometry
    (M : FiniteStrictProbabilityMap X Y P Q) :
    FiniteProbabilityL2Carrier Y →ₗᵢ[ℝ] FiniteProbabilityL2Carrier X where
  toLinearMap := M.l2PullbackLinearMap
  norm_map' := by
    intro y
    have hsquare := M.norm_sq_l2PullbackLinearMap y
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsquare

/-- Identity finite probability map. -/
def id
    (P : FiniteStrictProbabilityL2Data X) :
    FiniteStrictProbabilityMap X X P P where
  toFun := fun x => x
  weight_pushforward := by
    classical
    intro y
    unfold finiteProbabilityPushforwardWeight
    simp

/-- Composition of exact finite probability maps is again an exact finite
probability map. -/
def comp
    (M : FiniteStrictProbabilityMap X Y P Q)
    (N : FiniteStrictProbabilityMap Y Z Q R) :
    FiniteStrictProbabilityMap X Z P R where
  toFun := N.toFun ∘ M.toFun
  weight_pushforward := by
    classical
    intro z
    have h := M.weighted_sum_comp
      (fun y : Y => if N.toFun y = z then (1 : ℝ) else 0)
    have hN := N.weight_pushforward z
    unfold finiteProbabilityPushforwardWeight at hN ⊢
    calc
      (∑ x : X,
          if (N.toFun ∘ M.toFun) x = z then P.weight x else 0) =
        ∑ x : X, P.weight x *
          (if N.toFun (M.toFun x) = z then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro x _hx
          by_cases hx : N.toFun (M.toFun x) = z
          · simp [Function.comp_apply, hx]
          · simp [Function.comp_apply, hx]
      _ = ∑ y : Y, Q.weight y *
          (if N.toFun y = z then (1 : ℝ) else 0) := h
      _ = ∑ y : Y,
          if N.toFun y = z then Q.weight y else 0 := by
          apply Finset.sum_congr rfl
          intro y _hy
          by_cases hy : N.toFun y = z
          · simp [hy]
          · simp [hy]
      _ = R.weight z := hN

@[simp] theorem comp_toFun
    (M : FiniteStrictProbabilityMap X Y P Q)
    (N : FiniteStrictProbabilityMap Y Z Q R)
    (x : X) :
    (M.comp N).toFun x = N.toFun (M.toFun x) :=
  rfl

/-- The `L²` pullback is contravariantly functorial: pullback along a composite
is exactly the composite of the two pullback isometries. -/
theorem l2PullbackLinearMap_comp
    (M : FiniteStrictProbabilityMap X Y P Q)
    (N : FiniteStrictProbabilityMap Y Z Q R)
    (z : FiniteProbabilityL2Carrier Z) :
    M.l2PullbackLinearMap (N.l2PullbackLinearMap z) =
      (M.comp N).l2PullbackLinearMap z := by
  let h : Z → ℝ := R.coordinateObserveLinearMap z
  have hN :
      N.l2PullbackLinearMap z =
        Q.observableEmbedLinearMap (N.observablePullbackLinearMap h) := rfl
  rw [hN]
  change
    P.observableEmbedLinearMap
        (M.observablePullbackLinearMap
          (Q.coordinateObserveLinearMap
            (Q.observableEmbedLinearMap
              (N.observablePullbackLinearMap h)))) =
      P.observableEmbedLinearMap
        ((M.comp N).observablePullbackLinearMap h)
  rw [Q.coordinateObserve_observableEmbed]
  rfl

/-- Identity pullback is literally the identity on finite probability `L²`. -/
theorem l2PullbackLinearMap_id
    (P : FiniteStrictProbabilityL2Data X)
    (x : FiniteProbabilityL2Carrier X) :
    (FiniteStrictProbabilityMap.id P).l2PullbackLinearMap x = x := by
  ext i
  rw [l2PullbackLinearMap_apply]
  change
    Real.sqrt (P.weight i) *
        (x i / Real.sqrt (P.weight i)) = x i
  field_simp [P.sqrt_weight_ne_zero i]

end FiniteStrictProbabilityMap

end

end MathlibAnalytic
end MGAP4D
