import MGAP4D.MathlibAnalytic.FiniteRealProbabilityMixtureCouplingCost
import MGAP4D.MathlibAnalytic.FiniteRealProbabilityOverlapCouplingDisagreement
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

namespace FiniteRealCouplingData

variable {ι : Type} [DecidableEq ι] [Fintype ι]
variable {P Q : FiniteRealProbabilityData ι}

/-- Total coupling mass carried by unequal latent-index pairs. -/
def offDiagonalMass
    (C : FiniteRealCouplingData P Q) : ℝ :=
  ∑ i : ι, ∑ j : ι, if i = j then 0 else C.joint i j

/-- Off-diagonal mass is exactly the previously defined disagreement mass. -/
theorem offDiagonalMass_eq_disagreementMass
    (C : FiniteRealCouplingData P Q) :
    C.offDiagonalMass = C.disagreementMass := by
  unfold offDiagonalMass disagreementMass diagonalMass
  calc
    (∑ i : ι, ∑ j : ι, if i = j then 0 else C.joint i j) =
        ∑ i : ι, ∑ j : ι,
          (C.joint i j - if i = j then C.joint i j else 0) := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases hEq : i = j <;> simp [hEq]
    _ = ∑ i : ι,
          ((∑ j : ι, C.joint i j) -
            ∑ j : ι, if i = j then C.joint i j else 0) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.sum_sub_distrib]
    _ = (∑ i : ι, ∑ j : ι, C.joint i j) -
        ∑ i : ι, ∑ j : ι,
          if i = j then C.joint i j else 0 := by
      rw [Finset.sum_sub_distrib]
    _ = 1 - ∑ i : ι, C.joint i i := by
      rw [C.totalMass_eq_one]
      congr 1
      apply Finset.sum_congr rfl
      intro i _hi
      simp

end FiniteRealCouplingData

/-- Diagonal latent-index contribution to the expected cost of a finite
mixture coupling. -/
def finiteRealProbabilityMixtureCouplingDiagonalExpectedCost
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
    (cost : G → G → ℝ) : ℝ :=
  ∑ i : ι,
    indexCoupling.joint i i *
      (componentCoupling i i).expectedCost cost

/-- Off-diagonal latent-index contribution to the expected cost of a finite
mixture coupling. -/
def finiteRealProbabilityMixtureCouplingOffDiagonalExpectedCost
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
    (cost : G → G → ℝ) : ℝ :=
  ∑ i : ι, ∑ j : ι,
    if i = j then 0 else
      indexCoupling.joint i j *
        (componentCoupling i j).expectedCost cost

/-- Exact decomposition of finite-mixture expected cost into equal-index and
unequal-index contributions. -/
theorem finiteRealProbabilityMixtureCoupling_expectedCost_eq_diagonal_add_offDiagonal
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
      finiteRealProbabilityMixtureCouplingDiagonalExpectedCost
          indexCoupling componentCoupling cost +
        finiteRealProbabilityMixtureCouplingOffDiagonalExpectedCost
          indexCoupling componentCoupling cost := by
  classical
  rw [finiteRealProbabilityMixtureCoupling_expectedCost_eq]
  unfold finiteRealProbabilityMixtureCouplingDiagonalExpectedCost
    finiteRealProbabilityMixtureCouplingOffDiagonalExpectedCost
  let term : ι → ι → ℝ := fun i j =>
    indexCoupling.joint i j *
      (componentCoupling i j).expectedCost cost
  calc
    (∑ i : ι, ∑ j : ι, term i j) =
        ∑ i : ι, ∑ j : ι,
          ((if i = j then term i j else 0) +
            (if i = j then 0 else term i j)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases hEq : i = j <;> simp [hEq]
    _ =
        (∑ i : ι, ∑ j : ι, if i = j then term i j else 0) +
          ∑ i : ι, ∑ j : ι, if i = j then 0 else term i j := by
      simp_rw [Finset.sum_add_distrib]
    _ =
        (∑ i : ι, term i i) +
          ∑ i : ι, ∑ j : ι, if i = j then 0 else term i j := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _hi
      simp
    _ =
        (∑ i : ι,
          indexCoupling.joint i i *
            (componentCoupling i i).expectedCost cost) +
          ∑ i : ι, ∑ j : ι,
            if i = j then 0 else
              indexCoupling.joint i j *
                (componentCoupling i j).expectedCost cost := by
      rfl

/-- Equal-index component bounds and a uniform unequal-index bound combine
with the latent coupling disagreement mass to control the full mixture cost. -/
theorem finiteRealProbabilityMixtureCoupling_expectedCost_le_diagonal_add_disagreement
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
    (diagonalBound : ι → ℝ)
    (offDiagonalBound : ℝ)
    (hDiagonal : ∀ i : ι,
      (componentCoupling i i).expectedCost cost ≤ diagonalBound i)
    (hOffDiagonal : ∀ i j : ι, i ≠ j →
      (componentCoupling i j).expectedCost cost ≤ offDiagonalBound) :
    (finiteRealProbabilityMixtureCouplingData
        indexCoupling componentCoupling).expectedCost cost ≤
      (∑ i : ι,
        indexCoupling.joint i i * diagonalBound i) +
        indexCoupling.disagreementMass * offDiagonalBound := by
  rw [finiteRealProbabilityMixtureCoupling_expectedCost_eq_diagonal_add_offDiagonal]
  apply add_le_add
  · unfold finiteRealProbabilityMixtureCouplingDiagonalExpectedCost
    exact Finset.sum_le_sum fun i _hi =>
      mul_le_mul_of_nonneg_left
        (hDiagonal i) (indexCoupling.joint_nonneg i i)
  · unfold finiteRealProbabilityMixtureCouplingOffDiagonalExpectedCost
    calc
      (∑ i : ι, ∑ j : ι,
        if i = j then 0 else
          indexCoupling.joint i j *
            (componentCoupling i j).expectedCost cost) ≤
          ∑ i : ι, ∑ j : ι,
            if i = j then 0 else
              indexCoupling.joint i j * offDiagonalBound := by
        apply Finset.sum_le_sum
        intro i _hi
        apply Finset.sum_le_sum
        intro j _hj
        by_cases hEq : i = j
        · simp [hEq]
        · simp only [hEq, if_false]
          exact mul_le_mul_of_nonneg_left
            (hOffDiagonal i j hEq)
            (indexCoupling.joint_nonneg i j)
      _ = ∑ i : ι,
          (∑ j : ι, if i = j then 0 else indexCoupling.joint i j) *
            offDiagonalBound := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _hj
        by_cases hEq : i = j <;> simp [hEq]
      _ = (∑ i : ι, ∑ j : ι,
          if i = j then 0 else indexCoupling.joint i j) *
            offDiagonalBound := by
        rw [Finset.sum_mul]
      _ = indexCoupling.disagreementMass * offDiagonalBound := by
        rw [← indexCoupling.offDiagonalMass_eq_disagreementMass]
        rfl

end

end MathlibAnalytic
end MGAP4D
