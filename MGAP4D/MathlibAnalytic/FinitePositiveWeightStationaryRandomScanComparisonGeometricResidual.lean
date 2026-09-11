import MGAP4D.MathlibAnalytic.FinitePositiveWeightStationaryRandomScanComparisonIteration
import MGAP4D.MathlibAnalytic.FiniteProductKernelCouplingVariation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A declared coordinate-variation profile bounds every pairwise observable
difference by its total mass. -/
theorem FiniteProductVariationBound.difference_abs_le_totalVariation
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    {f : (ι → G) → ℝ}
    (P : FiniteProductVariationBound f)
    (A B : ι → G) :
    |f A - f B| ≤ finiteProductVariationTotal P.variation := by
  classical
  calc
    |f A - f B| ≤
        ∑ e : ι,
          finiteProductMismatchIndicator A B e * P.variation e :=
      P.difference_abs_le_mismatch_sum A B
    _ ≤ ∑ e : ι, P.variation e := by
      apply Finset.sum_le_sum
      intro e _he
      by_cases hEq : A e = B e
      · simp [finiteProductMismatchIndicator, hEq,
          P.variation_nonneg e]
      · simp [finiteProductMismatchIndicator, hEq]
    _ = finiteProductVariationTotal P.variation := rfl

/-- Every positive-weight normalized global expectation fixes constants. -/
theorem finitePositiveWeightGlobalExpectation_const
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (c : ℝ) :
    finitePositiveWeightGlobalExpectation weight (fun _ => c) = c := by
  unfold finitePositiveWeightGlobalExpectation
  rw [← Finset.sum_mul,
    finitePositiveWeightGlobalProbability_sum_eq_one weight hweight]
  ring

namespace FinitePositiveWeightStationaryRandomScanComparisonData

variable
  {ι G : Type}
  [DecidableEq ι]
  [Fintype ι]
  [Fintype G]
  [Nonempty G]
  {leftWeight rightWeight : (ι → G) → ℝ}

/-- The discrepancy of any two positive normalized expectations is bounded by
twice the total declared variation of the observable. -/
theorem expectationDiscrepancy_le_two_mul_totalVariation
    {f : (ι → G) → ℝ}
    (P : FiniteProductVariationBound f)
    (C : FinitePositiveWeightStationaryRandomScanComparisonData
      leftWeight rightWeight) :
    C.expectationDiscrepancy f ≤
      2 * finiteProductVariationTotal P.variation := by
  let g₀ : G := Classical.choice (inferInstance : Nonempty G)
  let A₀ : ι → G := fun _ => g₀
  let centered : (ι → G) → ℝ := fun A => f A - f A₀
  have hCentered (A : ι → G) :
      |centered A| ≤ finiteProductVariationTotal P.variation := by
    simpa [centered] using P.difference_abs_le_totalVariation A A₀
  have hLeft :
      |finitePositiveWeightGlobalExpectation leftWeight centered| ≤
        finiteProductVariationTotal P.variation :=
    finitePositiveWeightGlobalExpectation_abs_le
      leftWeight C.leftWeight_pos centered
      (finiteProductVariationTotal P.variation) hCentered
  have hRight :
      |finitePositiveWeightGlobalExpectation rightWeight centered| ≤
        finiteProductVariationTotal P.variation :=
    finitePositiveWeightGlobalExpectation_abs_le
      rightWeight C.rightWeight_pos centered
      (finiteProductVariationTotal P.variation) hCentered
  have hLeftCenter :
      finitePositiveWeightGlobalExpectation leftWeight centered =
        finitePositiveWeightGlobalExpectation leftWeight f - f A₀ := by
    calc
      finitePositiveWeightGlobalExpectation leftWeight centered =
          finitePositiveWeightGlobalExpectation leftWeight
            (fun A => f A - (fun _ : ι → G => f A₀) A) := rfl
      _ = finitePositiveWeightGlobalExpectation leftWeight f -
          finitePositiveWeightGlobalExpectation leftWeight
            (fun _ : ι → G => f A₀) :=
        finitePositiveWeightGlobalExpectation_sub leftWeight f
          (fun _ : ι → G => f A₀)
      _ = finitePositiveWeightGlobalExpectation leftWeight f - f A₀ := by
        rw [finitePositiveWeightGlobalExpectation_const
          leftWeight C.leftWeight_pos]
  have hRightCenter :
      finitePositiveWeightGlobalExpectation rightWeight centered =
        finitePositiveWeightGlobalExpectation rightWeight f - f A₀ := by
    calc
      finitePositiveWeightGlobalExpectation rightWeight centered =
          finitePositiveWeightGlobalExpectation rightWeight
            (fun A => f A - (fun _ : ι → G => f A₀) A) := rfl
      _ = finitePositiveWeightGlobalExpectation rightWeight f -
          finitePositiveWeightGlobalExpectation rightWeight
            (fun _ : ι → G => f A₀) :=
        finitePositiveWeightGlobalExpectation_sub rightWeight f
          (fun _ : ι → G => f A₀)
      _ = finitePositiveWeightGlobalExpectation rightWeight f - f A₀ := by
        rw [finitePositiveWeightGlobalExpectation_const
          rightWeight C.rightWeight_pos]
  have hTranslate :
      finitePositiveWeightGlobalExpectation leftWeight f -
          finitePositiveWeightGlobalExpectation rightWeight f =
        finitePositiveWeightGlobalExpectation leftWeight centered -
          finitePositiveWeightGlobalExpectation rightWeight centered := by
    calc
      finitePositiveWeightGlobalExpectation leftWeight f -
          finitePositiveWeightGlobalExpectation rightWeight f =
        (finitePositiveWeightGlobalExpectation leftWeight f - f A₀) -
          (finitePositiveWeightGlobalExpectation rightWeight f - f A₀) := by
            ring
      _ = finitePositiveWeightGlobalExpectation leftWeight centered -
          finitePositiveWeightGlobalExpectation rightWeight centered := by
            rw [hLeftCenter, hRightCenter]
  unfold expectationDiscrepancy
  rw [hTranslate]
  calc
    |finitePositiveWeightGlobalExpectation leftWeight centered -
        finitePositiveWeightGlobalExpectation rightWeight centered| =
      |finitePositiveWeightGlobalExpectation leftWeight centered +
        (-finitePositiveWeightGlobalExpectation rightWeight centered)| := by
          ring
    _ ≤ |finitePositiveWeightGlobalExpectation leftWeight centered| +
        |-finitePositiveWeightGlobalExpectation rightWeight centered| :=
      abs_add_le _ _
    _ = |finitePositiveWeightGlobalExpectation leftWeight centered| +
        |finitePositiveWeightGlobalExpectation rightWeight centered| := by
      rw [abs_neg]
    _ ≤ finiteProductVariationTotal P.variation +
        finiteProductVariationTotal P.variation :=
      add_le_add hLeft hRight
    _ = 2 * finiteProductVariationTotal P.variation := by ring

/-- The expectation discrepancy after `n` right-weight random-scan steps is
bounded by the geometric Dobrushin residual. -/
theorem expectationDiscrepancy_iterate_le_geometricResidual
    {f : (ι → G) → ℝ}
    (P : FiniteProductVariationBound f)
    (C : FinitePositiveWeightStationaryRandomScanComparisonData
      leftWeight rightWeight)
    (n : ℕ) :
    C.expectationDiscrepancy (C.rightRandomScanObservableIterate f n) ≤
      2 * finitePositiveWeightDobrushinRandomScanRate C.rightDobrushin ^ n *
        finiteProductVariationTotal P.variation := by
  have hBase :=
    expectationDiscrepancy_le_two_mul_totalVariation
      (rightRandomScanIterateVariationBound P C n) C
  have hContract :=
    rightRandomScanIterate_totalVariation_le_rate_pow P C n
  calc
    C.expectationDiscrepancy (C.rightRandomScanObservableIterate f n) ≤
        2 * finiteProductVariationTotal
          (rightRandomScanIterateVariationBound P C n).variation := hBase
    _ ≤ 2 *
        (finitePositiveWeightDobrushinRandomScanRate C.rightDobrushin ^ n *
          finiteProductVariationTotal P.variation) :=
      mul_le_mul_of_nonneg_left hContract (by norm_num)
    _ = 2 * finitePositiveWeightDobrushinRandomScanRate C.rightDobrushin ^ n *
        finiteProductVariationTotal P.variation := by ring

/-- Finite stationary comparison with an explicit geometric terminal residual.
The source contribution remains the exact accumulated local pairing. -/
theorem expectationDiscrepancy_le_partialSource_add_geometricResidual
    {f : (ι → G) → ℝ}
    (P : FiniteProductVariationBound f)
    (C : FinitePositiveWeightStationaryRandomScanComparisonData
      leftWeight rightWeight)
    (n : ℕ) :
    C.expectationDiscrepancy f ≤
      partialStationarySource P C n +
        2 * finitePositiveWeightDobrushinRandomScanRate C.rightDobrushin ^ n *
          finiteProductVariationTotal P.variation := by
  have hFinite :=
    expectationDiscrepancy_le_partialSource_add_iterateResidual P C n
  have hResidual :=
    expectationDiscrepancy_iterate_le_geometricResidual P C n
  exact hFinite.trans
    (add_le_add (le_refl (partialStationarySource P C n)) hResidual)

end FinitePositiveWeightStationaryRandomScanComparisonData

end

end MathlibAnalytic
end MGAP4D
