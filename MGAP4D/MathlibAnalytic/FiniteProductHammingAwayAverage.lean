import MGAP4D.MathlibAnalytic.FinitePositiveWeightsRandomScanCouplingHammingExpectation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators
noncomputable section

/-- Summing the real coordinate-disagreement indicators gives the real
Hamming distance. -/
theorem finiteRealDisagreementIndicator_sum_eq_hamming
    {ι G : Type} [DecidableEq ι] [DecidableEq G] [Fintype ι]
    (A B : ι → G) :
    (∑ target : ι,
      finiteRealDisagreementIndicator (A target) (B target)) =
      finiteProductHammingDistanceReal A B := by
  classical
  unfold finiteRealDisagreementIndicator
    finiteProductHammingDistanceReal finiteProductDisagreementFinset
  calc
    (∑ target : ι, if A target ≠ B target then (1 : ℝ) else 0) =
        ∑ target ∈ Finset.univ.filter (fun i : ι => A i ≠ B i),
          (1 : ℝ) := by
      rw [Finset.sum_filter]
    _ = ((Finset.univ.filter (fun i : ι => A i ≠ B i)).card : ℝ) := by
      simp

/-- Summing the Hamming cost away from the selected coordinate counts every
original disagreement once for each other coordinate. -/
theorem finiteProductHammingAwayReal_sum_eq_card_sub_one_mul_hamming
    {ι G : Type} [DecidableEq ι] [DecidableEq G] [Fintype ι]
    (A B : ι → G) :
    (∑ target : ι, finiteProductHammingAwayReal A B target) =
      ((Fintype.card ι : ℝ) - 1) *
        finiteProductHammingDistanceReal A B := by
  classical
  have hTarget (target : ι) :
      finiteProductHammingAwayReal A B target =
        finiteProductHammingDistanceReal A B -
          finiteRealDisagreementIndicator (A target) (B target) := by
    have hDecomposition :=
      finiteProductHammingDistanceReal_eq_away_add_indicator
        A B target
    linarith
  calc
    (∑ target : ι, finiteProductHammingAwayReal A B target) =
        ∑ target : ι,
          (finiteProductHammingDistanceReal A B -
            finiteRealDisagreementIndicator (A target) (B target)) := by
      apply Finset.sum_congr rfl
      intro target _
      exact hTarget target
    _ = (∑ _target : ι, finiteProductHammingDistanceReal A B) -
        ∑ target : ι,
          finiteRealDisagreementIndicator (A target) (B target) := by
      rw [Finset.sum_sub_distrib]
    _ = (Fintype.card ι : ℝ) *
          finiteProductHammingDistanceReal A B -
        finiteProductHammingDistanceReal A B := by
      rw [finiteRealDisagreementIndicator_sum_eq_hamming]
      simp
    _ = ((Fintype.card ι : ℝ) - 1) *
        finiteProductHammingDistanceReal A B := by
      ring

/-- The uniform average of the Hamming-away cost is exactly
`(1 - card⁻¹) × Hamming`. -/
theorem finiteProductHammingAwayReal_average_eq_one_sub_inv_mul_hamming
    {ι G : Type} [DecidableEq ι] [DecidableEq G] [Fintype ι]
    (hCard : 0 < Fintype.card ι)
    (A B : ι → G) :
    (Fintype.card ι : ℝ)⁻¹ *
        ∑ target : ι, finiteProductHammingAwayReal A B target =
      (1 - (Fintype.card ι : ℝ)⁻¹) *
        finiteProductHammingDistanceReal A B := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hCard)
  rw [finiteProductHammingAwayReal_sum_eq_card_sub_one_mul_hamming]
  field_simp [hn]

end
end MathlibAnalytic
end MGAP4D
