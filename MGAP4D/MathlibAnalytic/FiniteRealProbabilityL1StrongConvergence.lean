import MGAP4D.MathlibAnalytic.FinitePositiveWeightRandomScanErgodicConvergence
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter
open scoped BigOperators

noncomputable section

/-- Local finite real triangle inequality for sums. -/
theorem finiteRealProbability_abs_sum_le_sum_abs
    {G : Type} (s : Finset G) (u : G → ℝ) :
    |(∑ g in s, u g)| ≤ ∑ g in s, |u g| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert g s hg ih =>
      rw [Finset.sum_insert hg, Finset.sum_insert hg]
      exact le_trans (abs_add_le _ _) (add_le_add (le_refl _) ih)

namespace FiniteRealProbabilityData

variable {G : Type} [DecidableEq G] [Fintype G]

/-- The absolute pointwise mass difference is bounded by the unhalved `L¹`
distance. -/
theorem probability_sub_abs_le_l1Distance
    (P Q : FiniteRealProbabilityData G)
    (configuration : G) :
    |P.probability configuration - Q.probability configuration| ≤
      P.l1Distance Q := by
  unfold l1Distance
  exact Finset.single_le_sum
    (fun g _hg => abs_nonneg
      (P.probability g - Q.probability g))
    (Finset.mem_univ configuration)

/-- The expectation difference of a uniformly bounded finite real observable
is controlled by unhalved `L¹` distance times the chosen bound. -/
theorem expectation_sub_abs_le_l1Distance_mul_bound
    (P Q : FiniteRealProbabilityData G)
    (f : G → ℝ)
    (M : ℝ)
    (hM : 0 ≤ M)
    (hBound : ∀ g : G, |f g| ≤ M) :
    |P.expectation f - Q.expectation f| ≤
      P.l1Distance Q * M := by
  unfold expectation
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ g : G,
        (P.probability g * f g - Q.probability g * f g)| =
      |∑ g : G,
        (P.probability g - Q.probability g) * f g| := by
      congr 1
      apply Finset.sum_congr rfl
      intro g _hg
      ring
    _ ≤ ∑ g : G,
        |(P.probability g - Q.probability g) * f g| :=
      finiteRealProbability_abs_sum_le_sum_abs Finset.univ
        (fun g : G =>
          (P.probability g - Q.probability g) * f g)
    _ = ∑ g : G,
        |P.probability g - Q.probability g| * |f g| := by
      apply Finset.sum_congr rfl
      intro g _hg
      rw [abs_mul]
    _ ≤ ∑ g : G,
        |P.probability g - Q.probability g| * M := by
      apply Finset.sum_le_sum
      intro g _hg
      exact mul_le_mul_of_nonneg_left
        (hBound g) (abs_nonneg _)
    _ = P.l1Distance Q * M := by
      unfold l1Distance
      rw [Finset.sum_mul]

end FiniteRealProbabilityData

/-- Strict finite random-scan contraction gives pointwise convergence of every
configuration probability to the stationary normalized Gibbs law. -/
theorem FinitePositiveWeightBidirectionalDobrushinL1MatrixData.randomScanIterate_probability_tendsto_stationary
    {ι A : Type} [DecidableEq ι] [DecidableEq A]
    [Fintype ι] [Fintype A] [Nonempty A]
    {weight : (ι → A) → ℝ}
    (B : FinitePositiveWeightBidirectionalDobrushinL1MatrixData weight)
    (hweight : ∀ X : ι → A, 0 < weight X)
    (hCard : 0 < Fintype.card ι)
    (initialLaw : FiniteRealProbabilityData (ι → A))
    (configuration : ι → A) :
    Tendsto
      (fun n : ℕ =>
        (finiteRealProbabilityKernelIterateData
          (finitePositiveWeightRandomScanProbabilityData
            weight hweight hCard)
          n initialLaw).probability configuration)
      atTop
      (nhds
        ((finitePositiveWeightGlobalProbabilityData
          weight hweight).probability configuration)) := by
  let stationary := finitePositiveWeightGlobalProbabilityData weight hweight
  let iterate := fun n : ℕ =>
    finiteRealProbabilityKernelIterateData
      (finitePositiveWeightRandomScanProbabilityData
        weight hweight hCard)
      n initialLaw
  have hL1 :
      Tendsto
        (fun n : ℕ => (iterate n).l1Distance stationary)
        atTop (nhds 0) := by
    simpa [iterate, stationary] using
      B.randomScanIterate_l1Distance_stationary_tendsto_zero
        hweight hCard initialLaw
  have hDifference :
      Tendsto
        (fun n : ℕ =>
          (iterate n).probability configuration -
            stationary.probability configuration)
        atTop (nhds 0) := by
    exact squeeze_zero_norm
      (fun n => by
        rw [Real.norm_eq_abs]
        exact (iterate n).probability_sub_abs_le_l1Distance
          stationary configuration)
      hL1
  have hStationary :
      Tendsto
        (fun _ : ℕ => stationary.probability configuration)
        atTop (nhds (stationary.probability configuration)) :=
    tendsto_const_nhds
  simpa [iterate, stationary] using hDifference.add hStationary

/-- Strict finite random-scan contraction gives convergence of every uniformly
bounded real observable expectation to the stationary normalized Gibbs
expectation. -/
theorem FinitePositiveWeightBidirectionalDobrushinL1MatrixData.randomScanIterate_expectation_tendsto_stationary
    {ι A : Type} [DecidableEq ι] [DecidableEq A]
    [Fintype ι] [Fintype A] [Nonempty A]
    {weight : (ι → A) → ℝ}
    (B : FinitePositiveWeightBidirectionalDobrushinL1MatrixData weight)
    (hweight : ∀ X : ι → A, 0 < weight X)
    (hCard : 0 < Fintype.card ι)
    (initialLaw : FiniteRealProbabilityData (ι → A))
    (f : (ι → A) → ℝ)
    (M : ℝ)
    (hM : 0 ≤ M)
    (hBound : ∀ X : ι → A, |f X| ≤ M) :
    Tendsto
      (fun n : ℕ =>
        (finiteRealProbabilityKernelIterateData
          (finitePositiveWeightRandomScanProbabilityData
            weight hweight hCard)
          n initialLaw).expectation f)
      atTop
      (nhds (finitePositiveWeightGlobalExpectation weight f)) := by
  let stationary := finitePositiveWeightGlobalProbabilityData weight hweight
  let iterate := fun n : ℕ =>
    finiteRealProbabilityKernelIterateData
      (finitePositiveWeightRandomScanProbabilityData
        weight hweight hCard)
      n initialLaw
  have hL1 :
      Tendsto
        (fun n : ℕ => (iterate n).l1Distance stationary)
        atTop (nhds 0) := by
    simpa [iterate, stationary] using
      B.randomScanIterate_l1Distance_stationary_tendsto_zero
        hweight hCard initialLaw
  have hEnvelope :
      Tendsto
        (fun n : ℕ => (iterate n).l1Distance stationary * M)
        atTop (nhds 0) := by
    simpa using hL1.mul_const M
  have hDifference :
      Tendsto
        (fun n : ℕ =>
          (iterate n).expectation f - stationary.expectation f)
        atTop (nhds 0) := by
    exact squeeze_zero_norm
      (fun n => by
        rw [Real.norm_eq_abs]
        exact (iterate n).expectation_sub_abs_le_l1Distance_mul_bound
          stationary f M hM hBound)
      hEnvelope
  have hStationary :
      Tendsto
        (fun _ : ℕ => stationary.expectation f)
        atTop (nhds (stationary.expectation f)) :=
    tendsto_const_nhds
  simpa [iterate, stationary,
    finitePositiveWeightGlobalProbabilityData,
    finitePositiveWeightGlobalExpectation,
    FiniteRealProbabilityData.expectation] using
      hDifference.add hStationary

end
end MathlibAnalytic
end MGAP4D
