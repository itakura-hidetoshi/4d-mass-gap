import MGAP4D.MathlibAnalytic.FiniteGroupUniformProbabilityPushforward
import MGAP4D.MathlibAnalytic.FiniteGroupOrbitProbabilityL2Realization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

namespace FiniteStrictProbabilityMap

variable
    {X Y A B : Type}
    [Fintype X]
    [Fintype Y]
    [Fintype A]
    [Fintype B]
    {PX : FiniteStrictProbabilityL2Data X}
    {PY : FiniteStrictProbabilityL2Data Y}
    {PA : FiniteStrictProbabilityL2Data A}
    {PB : FiniteStrictProbabilityL2Data B}

/-- A commuting square of exact finite probability maps descends the bottom
set map to an exact finite probability map.  The proof uses only finite
change-of-variables identities and does not count fibres of the descended map. -/
noncomputable def descendCommutingSquare
    (QX : FiniteStrictProbabilityMap X A PX PA)
    (M : FiniteStrictProbabilityMap X Y PX PY)
    (QY : FiniteStrictProbabilityMap Y B PY PB)
    (f : A → B)
    (hcomm : ∀ x : X, f (QX.toFun x) = QY.toFun (M.toFun x)) :
    FiniteStrictProbabilityMap A B PA PB where
  toFun := f
  weight_pushforward := by
    classical
    intro b
    unfold finiteProbabilityPushforwardWeight
    calc
      (∑ a : A, if f a = b then PA.weight a else 0) =
          ∑ a : A, PA.weight a *
            (if f a = b then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro a _ha
        by_cases hab : f a = b
        · simp [hab]
        · simp [hab]
      _ = ∑ x : X, PX.weight x *
            (if f (QX.toFun x) = b then (1 : ℝ) else 0) := by
        symm
        exact QX.weighted_sum_comp
          (fun a : A => if f a = b then (1 : ℝ) else 0)
      _ = ∑ x : X, PX.weight x *
            (if QY.toFun (M.toFun x) = b then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro x _hx
        rw [hcomm x]
      _ = ∑ y : Y, PY.weight y *
            (if QY.toFun y = b then (1 : ℝ) else 0) :=
        M.weighted_sum_comp
          (fun y : Y => if QY.toFun y = b then (1 : ℝ) else 0)
      _ = ∑ z : B, PB.weight z *
            (if z = b then (1 : ℝ) else 0) :=
        QY.weighted_sum_comp
          (fun z : B => if z = b then (1 : ℝ) else 0)
      _ = PB.weight b := by
        simp

@[simp] theorem descendCommutingSquare_toFun
    (QX : FiniteStrictProbabilityMap X A PX PA)
    (M : FiniteStrictProbabilityMap X Y PX PY)
    (QY : FiniteStrictProbabilityMap Y B PY PB)
    (f : A → B)
    (hcomm : ∀ x : X, f (QX.toFun x) = QY.toFun (M.toFun x))
    (a : A) :
    (descendCommutingSquare QX M QY f hcomm).toFun a = f a :=
  rfl

end FiniteStrictProbabilityMap

/-- The quotient-class map from a finite configuration type to its actual group
orbit quotient is itself an exact probability map from uniform configuration
probability to the pushforward orbit probability. -/
noncomputable def finiteGroupOrbitClassProbabilityMap
    (G α : Type)
    [Group G]
    [Fintype α]
    [Nonempty α]
    [MulAction G α] :
    FiniteStrictProbabilityMap
      α
      (FiniteGroupOrbitQuotient G α)
      (finiteUniformProbabilityL2Data α)
      (finiteGroupOrbitProbabilityL2Data G α) where
  toFun := finiteGroupOrbitClass G α
  weight_pushforward := by
    classical
    intro q
    unfold finiteProbabilityPushforwardWeight
    rw [finiteGroupOrbitProbabilityL2Data_weight_eq_pushforward]
    apply Finset.sum_congr rfl
    intro x _hx
    by_cases hqx : q = finiteGroupOrbitClass G α x
    · simp [hqx]
    · have hxq : finiteGroupOrbitClass G α x ≠ q := Ne.symm hqx
      simp [hqx, hxq]

@[simp] theorem finiteGroupOrbitClassProbabilityMap_toFun
    (G α : Type)
    [Group G]
    [Fintype α]
    [Nonempty α]
    [MulAction G α]
    (x : α) :
    (finiteGroupOrbitClassProbabilityMap G α).toFun x =
      finiteGroupOrbitClass G α x :=
  rfl

end

end MathlibAnalytic
end MGAP4D
