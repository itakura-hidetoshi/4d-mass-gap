import MGAP4D.MathlibAnalytic.FinitePositiveWeightStationaryRandomScanComparison
import MGAP4D.MathlibAnalytic.FinitePositiveWeightSingleSiteOverlapCoupling
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators
noncomputable section

/-- Full-configuration kernel obtained by resampling one coordinate. -/
def finitePositiveWeightSingleSiteUpdateKernel
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G]
    (weight : (ι → G) → ℝ) (input : ι → G) (target : ι)
    (output : ι → G) : ℝ :=
  ∑ g : G, if Function.update input target g = output then
    finitePositiveWeightSingleSiteProbability weight input target g else 0

theorem finitePositiveWeightSingleSiteUpdateKernel_nonneg
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G] [Nonempty G]
    (weight : (ι → G) → ℝ) (hweight : ∀ A : ι → G, 0 < weight A)
    (input : ι → G) (target : ι) (output : ι → G) :
    0 ≤ finitePositiveWeightSingleSiteUpdateKernel weight input target output := by
  unfold finitePositiveWeightSingleSiteUpdateKernel
  apply Finset.sum_nonneg
  intro g _
  by_cases h : Function.update input target g = output
  · simp [h, le_of_lt (finitePositiveWeightSingleSiteProbability_pos
      weight hweight input target g)]
  · simp [h]

theorem finitePositiveWeightSingleSiteUpdateKernel_sum_eq_one
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G] [Nonempty G]
    (weight : (ι → G) → ℝ) (hweight : ∀ A : ι → G, 0 < weight A)
    (input : ι → G) (target : ι) :
    ∑ output : ι → G,
      finitePositiveWeightSingleSiteUpdateKernel weight input target output = 1 := by
  classical
  unfold finitePositiveWeightSingleSiteUpdateKernel
  rw [Finset.sum_comm]
  simp [finitePositiveWeightSingleSiteProbability_sum_eq_one
    weight hweight input target]

theorem finitePositiveWeightSingleSiteUpdateKernel_expectation
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G]
    (weight : (ι → G) → ℝ) (input : ι → G) (target : ι)
    (f : (ι → G) → ℝ) :
    (∑ output : ι → G,
      finitePositiveWeightSingleSiteUpdateKernel weight input target output *
        f output) =
      finitePositiveWeightSingleSiteExpectation weight f input target := by
  classical
  unfold finitePositiveWeightSingleSiteUpdateKernel
    finitePositiveWeightSingleSiteExpectation
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  simp

/-- Uniform random-scan full-configuration kernel. -/
def finitePositiveWeightRandomScanKernel
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G]
    (weight : (ι → G) → ℝ) (input output : ι → G) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ target : ι,
    finitePositiveWeightSingleSiteUpdateKernel weight input target output

theorem finitePositiveWeightRandomScanKernel_nonneg
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G] [Nonempty G]
    (weight : (ι → G) → ℝ) (hweight : ∀ A : ι → G, 0 < weight A)
    (input output : ι → G) :
    0 ≤ finitePositiveWeightRandomScanKernel weight input output := by
  unfold finitePositiveWeightRandomScanKernel
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun target _ =>
      finitePositiveWeightSingleSiteUpdateKernel_nonneg
        weight hweight input target output)

theorem finitePositiveWeightRandomScanKernel_sum_eq_one
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G] [Nonempty G]
    (weight : (ι → G) → ℝ) (hweight : ∀ A : ι → G, 0 < weight A)
    (hCard : 0 < Fintype.card ι) (input : ι → G) :
    ∑ output : ι → G,
      finitePositiveWeightRandomScanKernel weight input output = 1 := by
  classical
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hCard)
  unfold finitePositiveWeightRandomScanKernel
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [finitePositiveWeightSingleSiteUpdateKernel_sum_eq_one
    weight hweight input]
  simp [hn]

theorem finitePositiveWeightRandomScanKernel_expectation
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G]
    (weight : (ι → G) → ℝ) (input : ι → G)
    (f : (ι → G) → ℝ) :
    (∑ output : ι → G,
      finitePositiveWeightRandomScanKernel weight input output * f output) =
      finitePositiveWeightRandomScanConditionalExpectation weight f input := by
  classical
  unfold finitePositiveWeightRandomScanKernel
    finitePositiveWeightRandomScanConditionalExpectation
  calc
    (∑ output : ι → G,
      ((Fintype.card ι : ℝ)⁻¹ * ∑ target : ι,
        finitePositiveWeightSingleSiteUpdateKernel weight input target output) *
        f output) =
      (Fintype.card ι : ℝ)⁻¹ * ∑ output : ι → G,
        (∑ target : ι,
          finitePositiveWeightSingleSiteUpdateKernel weight input target output) *
          f output := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro output _
      ring
    _ = (Fintype.card ι : ℝ)⁻¹ * ∑ target : ι,
        ∑ output : ι → G,
          finitePositiveWeightSingleSiteUpdateKernel weight input target output *
            f output := by
      congr 1
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = (Fintype.card ι : ℝ)⁻¹ * ∑ target : ι,
        finitePositiveWeightSingleSiteExpectation weight f input target := by
      congr 1
      apply Finset.sum_congr rfl
      intro target _
      exact finitePositiveWeightSingleSiteUpdateKernel_expectation
        weight input target f

noncomputable def finitePositiveWeightRandomScanProbabilityData
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G] [Nonempty G]
    (weight : (ι → G) → ℝ) (hweight : ∀ A : ι → G, 0 < weight A)
    (hCard : 0 < Fintype.card ι) (input : ι → G) :
    FiniteRealProbabilityData (ι → G) :=
  { probability := finitePositiveWeightRandomScanKernel weight input
    probability_nonneg :=
      finitePositiveWeightRandomScanKernel_nonneg weight hweight input
    probability_sum_eq_one :=
      finitePositiveWeightRandomScanKernel_sum_eq_one
        weight hweight hCard input }

/-- Pointwise stationarity of the normalized Gibbs law. -/
theorem finitePositiveWeightGlobalProbability_randomScan_stationary
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G] [Nonempty G]
    (weight : (ι → G) → ℝ) (hweight : ∀ A : ι → G, 0 < weight A)
    (hCard : 0 < Fintype.card ι) (output : ι → G) :
    (∑ input : ι → G,
      finitePositiveWeightGlobalProbability weight input *
        finitePositiveWeightRandomScanKernel weight input output) =
      finitePositiveWeightGlobalProbability weight output := by
  classical
  let indicator : (ι → G) → ℝ := fun A => if A = output then 1 else 0
  have h := finitePositiveWeightGlobalExpectation_randomScan
    weight hweight hCard indicator
  unfold finitePositiveWeightGlobalExpectation at h
  have hAction (input : ι → G) :
      finitePositiveWeightRandomScanConditionalExpectation weight indicator input =
        ∑ A : ι → G,
          finitePositiveWeightRandomScanKernel weight input A * indicator A :=
    (finitePositiveWeightRandomScanKernel_expectation
      weight input indicator).symm
  simp_rw [hAction] at h
  simpa [indicator] using h

end
end MathlibAnalytic
end MGAP4D
