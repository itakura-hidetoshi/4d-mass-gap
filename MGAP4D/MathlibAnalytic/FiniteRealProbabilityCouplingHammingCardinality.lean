import MGAP4D.MathlibAnalytic.FinitePositiveWeightConditionalL1Telescoping
import MGAP4D.MathlibAnalytic.FiniteRealProbabilityMixtureCouplingCost
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Real Hamming distance on a finite product is bounded by the number of
coordinates. -/
theorem finiteProductHammingDistanceReal_le_card
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [DecidableEq G]
    (A B : ι → G) :
    finiteProductHammingDistanceReal A B ≤ (Fintype.card ι : ℝ) := by
  unfold finiteProductHammingDistanceReal
  exact_mod_cast
    Finset.card_le_card
      (show finiteProductDisagreementFinset A B ⊆
          (Finset.univ : Finset ι) from Finset.subset_univ _)

namespace FiniteRealCouplingData

/-- Under any finite coupling of two product-valued laws, expected Hamming
cost is bounded by the number of product coordinates. -/
theorem expectedFiniteProductHamming_le_card
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [DecidableEq G]
    [Fintype G]
    {P Q : FiniteRealProbabilityData (ι → G)}
    (C : FiniteRealCouplingData P Q) :
    C.expectedCost finiteProductHammingDistanceReal ≤
      (Fintype.card ι : ℝ) := by
  unfold expectedCost
  calc
    (∑ A : ι → G, ∑ B : ι → G,
      C.joint A B * finiteProductHammingDistanceReal A B) ≤
        ∑ A : ι → G, ∑ B : ι → G,
          C.joint A B * (Fintype.card ι : ℝ) := by
      apply Finset.sum_le_sum
      intro A _hA
      apply Finset.sum_le_sum
      intro B _hB
      exact mul_le_mul_of_nonneg_left
        (finiteProductHammingDistanceReal_le_card A B)
        (C.joint_nonneg A B)
    _ = ∑ A : ι → G,
          (∑ B : ι → G, C.joint A B) *
            (Fintype.card ι : ℝ) := by
      apply Finset.sum_congr rfl
      intro A _hA
      rw [Finset.sum_mul]
    _ = (∑ A : ι → G, ∑ B : ι → G, C.joint A B) *
          (Fintype.card ι : ℝ) := by
      rw [Finset.sum_mul]
    _ = (Fintype.card ι : ℝ) := by
      rw [C.totalMass_eq_one, one_mul]

/-- Uniform boundedness package for finite-product Hamming cost. -/
theorem finiteProductHammingCardinalityPackage
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [DecidableEq G]
    [Fintype G]
    {P Q : FiniteRealProbabilityData (ι → G)}
    (C : FiniteRealCouplingData P Q) :
    (∀ A B : ι → G,
      finiteProductHammingDistanceReal A B ≤ (Fintype.card ι : ℝ)) ∧
    C.expectedCost finiteProductHammingDistanceReal ≤
      (Fintype.card ι : ℝ) := by
  exact ⟨finiteProductHammingDistanceReal_le_card,
    C.expectedFiniteProductHamming_le_card⟩

end FiniteRealCouplingData

end

end MathlibAnalytic
end MGAP4D
