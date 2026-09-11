import MGAP4D.MathlibAnalytic.FiniteRealProbabilityOverlapCoupling
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A finite convex mixture of finite real probability laws. -/
noncomputable def finiteRealProbabilityMixtureData
    {ι G : Type}
    [Fintype ι]
    [Fintype G]
    (indexLaw : FiniteRealProbabilityData ι)
    (componentLaw : ι → FiniteRealProbabilityData G) :
    FiniteRealProbabilityData G :=
  { probability := fun x =>
      ∑ i : ι, indexLaw.probability i * (componentLaw i).probability x
    probability_nonneg := fun x =>
      Finset.sum_nonneg fun i _hi =>
        mul_nonneg
          (indexLaw.probability_nonneg i)
          ((componentLaw i).probability_nonneg x)
    probability_sum_eq_one := by
      calc
        (∑ x : G,
          ∑ i : ι,
            indexLaw.probability i * (componentLaw i).probability x) =
            ∑ i : ι,
              ∑ x : G,
                indexLaw.probability i * (componentLaw i).probability x := by
          rw [Finset.sum_comm]
        _ = ∑ i : ι,
              indexLaw.probability i *
                ∑ x : G, (componentLaw i).probability x := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [Finset.mul_sum]
        _ = ∑ i : ι, indexLaw.probability i := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [(componentLaw i).probability_sum_eq_one, mul_one]
        _ = 1 := indexLaw.probability_sum_eq_one }

/-- Joint law obtained by first coupling latent mixture indices and then using
a prescribed coupling of every pair of component laws. -/
def finiteRealProbabilityMixtureCoupling
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [DecidableEq G]
    [Fintype G]
    {leftIndexLaw rightIndexLaw : FiniteRealProbabilityData ι}
    {leftComponentLaw rightComponentLaw : ι → FiniteRealProbabilityData G}
    (indexCoupling : FiniteRealCouplingData leftIndexLaw rightIndexLaw)
    (componentCoupling : ∀ i j : ι,
      FiniteRealCouplingData (leftComponentLaw i) (rightComponentLaw j))
    (x y : G) : ℝ :=
  ∑ i : ι, ∑ j : ι,
    indexCoupling.joint i j * (componentCoupling i j).joint x y

/-- The latent/component mixture coupling is nonnegative. -/
theorem finiteRealProbabilityMixtureCoupling_nonneg
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [DecidableEq G]
    [Fintype G]
    {leftIndexLaw rightIndexLaw : FiniteRealProbabilityData ι}
    {leftComponentLaw rightComponentLaw : ι → FiniteRealProbabilityData G}
    (indexCoupling : FiniteRealCouplingData leftIndexLaw rightIndexLaw)
    (componentCoupling : ∀ i j : ι,
      FiniteRealCouplingData (leftComponentLaw i) (rightComponentLaw j))
    (x y : G) :
    0 ≤ finiteRealProbabilityMixtureCoupling
      indexCoupling componentCoupling x y := by
  unfold finiteRealProbabilityMixtureCoupling
  exact Finset.sum_nonneg fun i _hi =>
    Finset.sum_nonneg fun j _hj =>
      mul_nonneg
        (indexCoupling.joint_nonneg i j)
        ((componentCoupling i j).joint_nonneg x y)

/-- The left marginal is exactly the left convex mixture. -/
theorem finiteRealProbabilityMixtureCoupling_leftMarginal
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [DecidableEq G]
    [Fintype G]
    {leftIndexLaw rightIndexLaw : FiniteRealProbabilityData ι}
    {leftComponentLaw rightComponentLaw : ι → FiniteRealProbabilityData G}
    (indexCoupling : FiniteRealCouplingData leftIndexLaw rightIndexLaw)
    (componentCoupling : ∀ i j : ι,
      FiniteRealCouplingData (leftComponentLaw i) (rightComponentLaw j))
    (x : G) :
    ∑ y : G,
      finiteRealProbabilityMixtureCoupling
        indexCoupling componentCoupling x y =
      (finiteRealProbabilityMixtureData
        leftIndexLaw leftComponentLaw).probability x := by
  unfold finiteRealProbabilityMixtureCoupling
    finiteRealProbabilityMixtureData
  calc
    (∑ y : G, ∑ i : ι, ∑ j : ι,
      indexCoupling.joint i j * (componentCoupling i j).joint x y) =
        ∑ i : ι, ∑ j : ι, ∑ y : G,
          indexCoupling.joint i j * (componentCoupling i j).joint x y := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.sum_comm]
    _ = ∑ i : ι, ∑ j : ι,
          indexCoupling.joint i j *
            (leftComponentLaw i).probability x := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      rw [← Finset.mul_sum, (componentCoupling i j).left_marginal x]
    _ = ∑ i : ι,
          leftIndexLaw.probability i *
            (leftComponentLaw i).probability x := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [← Finset.sum_mul, indexCoupling.left_marginal i]

/-- The right marginal is exactly the right convex mixture. -/
theorem finiteRealProbabilityMixtureCoupling_rightMarginal
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [DecidableEq G]
    [Fintype G]
    {leftIndexLaw rightIndexLaw : FiniteRealProbabilityData ι}
    {leftComponentLaw rightComponentLaw : ι → FiniteRealProbabilityData G}
    (indexCoupling : FiniteRealCouplingData leftIndexLaw rightIndexLaw)
    (componentCoupling : ∀ i j : ι,
      FiniteRealCouplingData (leftComponentLaw i) (rightComponentLaw j))
    (y : G) :
    ∑ x : G,
      finiteRealProbabilityMixtureCoupling
        indexCoupling componentCoupling x y =
      (finiteRealProbabilityMixtureData
        rightIndexLaw rightComponentLaw).probability y := by
  unfold finiteRealProbabilityMixtureCoupling
    finiteRealProbabilityMixtureData
  calc
    (∑ x : G, ∑ i : ι, ∑ j : ι,
      indexCoupling.joint i j * (componentCoupling i j).joint x y) =
        ∑ i : ι, ∑ j : ι, ∑ x : G,
          indexCoupling.joint i j * (componentCoupling i j).joint x y := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.sum_comm]
    _ = ∑ i : ι, ∑ j : ι,
          indexCoupling.joint i j *
            (rightComponentLaw j).probability y := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      rw [← Finset.mul_sum, (componentCoupling i j).right_marginal y]
    _ = ∑ j : ι, ∑ i : ι,
          indexCoupling.joint i j *
            (rightComponentLaw j).probability y := by
      rw [Finset.sum_comm]
    _ = ∑ j : ι,
          rightIndexLaw.probability j *
            (rightComponentLaw j).probability y := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [← Finset.sum_mul, indexCoupling.right_marginal j]

/-- Exact-marginal coupling data for two finite convex mixtures. -/
noncomputable def finiteRealProbabilityMixtureCouplingData
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [DecidableEq G]
    [Fintype G]
    {leftIndexLaw rightIndexLaw : FiniteRealProbabilityData ι}
    {leftComponentLaw rightComponentLaw : ι → FiniteRealProbabilityData G}
    (indexCoupling : FiniteRealCouplingData leftIndexLaw rightIndexLaw)
    (componentCoupling : ∀ i j : ι,
      FiniteRealCouplingData (leftComponentLaw i) (rightComponentLaw j)) :
    FiniteRealCouplingData
      (finiteRealProbabilityMixtureData leftIndexLaw leftComponentLaw)
      (finiteRealProbabilityMixtureData rightIndexLaw rightComponentLaw) :=
  { joint := finiteRealProbabilityMixtureCoupling
      indexCoupling componentCoupling
    joint_nonneg := finiteRealProbabilityMixtureCoupling_nonneg
      indexCoupling componentCoupling
    left_marginal := finiteRealProbabilityMixtureCoupling_leftMarginal
      indexCoupling componentCoupling
    right_marginal := finiteRealProbabilityMixtureCoupling_rightMarginal
      indexCoupling componentCoupling }

end

end MathlibAnalytic
end MGAP4D
