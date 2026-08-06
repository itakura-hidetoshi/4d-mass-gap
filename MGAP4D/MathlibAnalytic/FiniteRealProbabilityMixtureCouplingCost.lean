import MGAP4D.MathlibAnalytic.FiniteRealProbabilityMixtureCoupling
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

namespace FiniteRealCouplingData

variable {G : Type} [DecidableEq G] [Fintype G]
variable {P Q : FiniteRealProbabilityData G}

/-- Expected value of a real pair cost under a finite coupling. -/
def expectedCost
    (C : FiniteRealCouplingData P Q)
    (cost : G → G → ℝ) : ℝ :=
  ∑ x : G, ∑ y : G, C.joint x y * cost x y

end FiniteRealCouplingData

/-- Expected cost of a latent-index/component mixture coupling is exactly the
latent coupling average of the component-coupling expected costs. -/
theorem finiteRealProbabilityMixtureCoupling_expectedCost_eq
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
    (cost : G → G → ℝ) :
    (finiteRealProbabilityMixtureCouplingData
        indexCoupling componentCoupling).expectedCost cost =
      ∑ i : ι, ∑ j : ι,
        indexCoupling.joint i j *
          (componentCoupling i j).expectedCost cost := by
  classical
  unfold FiniteRealCouplingData.expectedCost
    finiteRealProbabilityMixtureCouplingData
    finiteRealProbabilityMixtureCoupling
  calc
    (∑ x : G, ∑ y : G,
      (∑ i : ι, ∑ j : ι,
        indexCoupling.joint i j *
          (componentCoupling i j).joint x y) * cost x y) =
        ∑ x : G, ∑ y : G, ∑ i : ι, ∑ j : ι,
          indexCoupling.joint i j *
            (componentCoupling i j).joint x y * cost x y := by
      apply Finset.sum_congr rfl
      intro x _hx
      apply Finset.sum_congr rfl
      intro y _hy
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.sum_mul]
    _ = ∑ x : G, ∑ i : ι, ∑ y : G, ∑ j : ι,
          indexCoupling.joint i j *
            (componentCoupling i j).joint x y * cost x y := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.sum_comm]
    _ = ∑ i : ι, ∑ x : G, ∑ y : G, ∑ j : ι,
          indexCoupling.joint i j *
            (componentCoupling i j).joint x y * cost x y := by
      rw [Finset.sum_comm]
    _ = ∑ i : ι, ∑ x : G, ∑ j : ι, ∑ y : G,
          indexCoupling.joint i j *
            (componentCoupling i j).joint x y * cost x y := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.sum_comm]
    _ = ∑ i : ι, ∑ j : ι, ∑ x : G, ∑ y : G,
          indexCoupling.joint i j *
            (componentCoupling i j).joint x y * cost x y := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.sum_comm]
    _ = ∑ i : ι, ∑ j : ι,
          indexCoupling.joint i j *
            (∑ x : G, ∑ y : G,
              (componentCoupling i j).joint x y * cost x y) := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _hy
      ring

/-- Componentwise expected-cost bounds pass through a finite mixture coupling
with the latent coupling weights. -/
theorem finiteRealProbabilityMixtureCoupling_expectedCost_le
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
    (cost : G → G → ℝ)
    (bound : ι → ι → ℝ)
    (hBound : ∀ i j : ι,
      (componentCoupling i j).expectedCost cost ≤ bound i j) :
    (finiteRealProbabilityMixtureCouplingData
        indexCoupling componentCoupling).expectedCost cost ≤
      ∑ i : ι, ∑ j : ι,
        indexCoupling.joint i j * bound i j := by
  rw [finiteRealProbabilityMixtureCoupling_expectedCost_eq]
  apply Finset.sum_le_sum
  intro i _hi
  apply Finset.sum_le_sum
  intro j _hj
  exact mul_le_mul_of_nonneg_left
    (hBound i j) (indexCoupling.joint_nonneg i j)

end

end MathlibAnalytic
end MGAP4D
