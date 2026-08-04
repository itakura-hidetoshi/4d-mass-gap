import MGAP4D.MathlibAnalytic.FinitePositiveWeightCrossWeightRandomScanComparison
import MGAP4D.MathlibAnalytic.FinitePositiveWeightRandomScanReversibility
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Total mass of a finite product weight. -/
def finitePositiveWeightTotalMass
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ) : ℝ :=
  ∑ A : ι → G, weight A

/-- A strictly positive finite product weight has strictly positive total
mass. -/
theorem finitePositiveWeightTotalMass_pos
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A) :
    0 < finitePositiveWeightTotalMass weight := by
  classical
  unfold finitePositiveWeightTotalMass
  apply Finset.sum_pos
  · intro A _hA
    exact hweight A
  · exact Finset.univ_nonempty

/-- Normalized expectation associated with a strictly positive finite product
weight. -/
def finitePositiveWeightExpectation
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (f : (ι → G) → ℝ) : ℝ :=
  (finitePositiveWeightTotalMass weight)⁻¹ *
    ∑ A : ι → G, weight A * f A

/-- Normalized expectation is linear over subtraction. -/
theorem finitePositiveWeightExpectation_sub
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (f g : (ι → G) → ℝ) :
    finitePositiveWeightExpectation weight (f - g) =
      finitePositiveWeightExpectation weight f -
        finitePositiveWeightExpectation weight g := by
  classical
  unfold finitePositiveWeightExpectation
  simp only [Pi.sub_apply]
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro A _hA
  ring

/-- A uniform pointwise absolute bound passes to normalized positive-weight
expectation. -/
theorem finitePositiveWeightExpectation_abs_le_of_pointwise
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (f : (ι → G) → ℝ)
    (bound : ℝ)
    (hbound : 0 ≤ bound)
    (hf : ∀ A : ι → G, |f A| ≤ bound) :
    |finitePositiveWeightExpectation weight f| ≤ bound := by
  classical
  let mass := finitePositiveWeightTotalMass weight
  have hMassPos : 0 < mass :=
    finitePositiveWeightTotalMass_pos weight hweight
  have hMassNonneg : 0 ≤ mass⁻¹ := (inv_pos.mpr hMassPos).le
  have hSumAbs :
      |∑ A : ι → G, weight A * f A| ≤
        ∑ A : ι → G, weight A * |f A| := by
    calc
      |∑ A : ι → G, weight A * f A| ≤
          ∑ A : ι → G, |weight A * f A| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ A : ι → G, weight A * |f A| := by
        apply Finset.sum_congr rfl
        intro A _hA
        rw [abs_mul, abs_of_pos (hweight A)]
  have hWeighted :
      (∑ A : ι → G, weight A * |f A|) ≤
        ∑ A : ι → G, weight A * bound := by
    apply Finset.sum_le_sum
    intro A _hA
    exact mul_le_mul_of_nonneg_left (hf A) (hweight A).le
  unfold finitePositiveWeightExpectation
  change |mass⁻¹ * ∑ A : ι → G, weight A * f A| ≤ bound
  rw [abs_mul, abs_of_pos (inv_pos.mpr hMassPos)]
  calc
    mass⁻¹ * |∑ A : ι → G, weight A * f A| ≤
        mass⁻¹ * ∑ A : ι → G, weight A * |f A| :=
      mul_le_mul_of_nonneg_left hSumAbs hMassNonneg
    _ ≤ mass⁻¹ * ∑ A : ι → G, weight A * bound :=
      mul_le_mul_of_nonneg_left hWeighted hMassNonneg
    _ = mass⁻¹ * (mass * bound) := by
      unfold mass finitePositiveWeightTotalMass
      rw [Finset.sum_mul]
    _ = bound := by
      field_simp [ne_of_gt hMassPos]

/-- Exact one-site conditional expectation preserves the constant one
observable. -/
theorem finitePositiveWeightSingleSiteExpectation_one
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (A : ι → G)
    (target : ι) :
    finitePositiveWeightSingleSiteExpectation weight (fun _ => 1) A target = 1 := by
  unfold finitePositiveWeightSingleSiteExpectation
  simpa using
    finitePositiveWeightSingleSiteProbability_sum_eq_one
      weight hweight A target

/-- On a nonempty coordinate type, uniform random scan preserves the constant
one observable. -/
theorem finitePositiveWeightRandomScan_one
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty ι]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A) :
    finitePositiveWeightRandomScanConditionalExpectation
      weight (fun _ => 1) = fun _ => 1 := by
  funext A
  unfold finitePositiveWeightRandomScanConditionalExpectation
  simp_rw [finitePositiveWeightSingleSiteExpectation_one weight hweight A]
  have hCard : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [hCard]

/-- A positive-weight normalized expectation is stationary under its exact
uniform random-scan Gibbs sampler. -/
theorem finitePositiveWeightExpectation_randomScan_eq
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty ι]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (f : (ι → G) → ℝ) :
    finitePositiveWeightExpectation weight
        (finitePositiveWeightRandomScanConditionalExpectation weight f) =
      finitePositiveWeightExpectation weight f := by
  have hPairing :=
    finitePositiveWeightRandomScan_pairing_symm
      weight f (fun _ => 1)
  have hOne := finitePositiveWeightRandomScan_one weight hweight
  unfold finitePositiveWeightExpectation
  congr 1
  simpa [finitePositiveWeightPairing, hOne] using hPairing

/-- One stationary cross-weight comparison step.  The boundary/source error is
kept as its local pairing with the observable variation profile; the residual
is the same expectation discrepancy after applying the right-weight random
scan once. -/
theorem FiniteProductVariationBound.expectation_crossWeight_difference_abs_le_sourcePairing_add_randomScanResidual
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty ι]
    [Nonempty G]
    (leftWeight rightWeight : (ι → G) → ℝ)
    (hLeftWeight : ∀ A : ι → G, 0 < leftWeight A)
    (hRightWeight : ∀ A : ι → G, 0 < rightWeight A)
    {f : (ι → G) → ℝ}
    (P : FiniteProductVariationBound f)
    (sourceBound : ι → ℝ)
    (hSourceBound : ∀ target : ι, 0 ≤ sourceBound target)
    (hCrossL1 :
      ∀ (A : ι → G) (target : ι),
        finitePositiveWeightSingleSiteConditionalCrossL1
            leftWeight rightWeight A target ≤
          sourceBound target) :
    |finitePositiveWeightExpectation leftWeight f -
        finitePositiveWeightExpectation rightWeight f| ≤
      (Fintype.card ι : ℝ)⁻¹ *
          ∑ target : ι,
            sourceBound target * P.variation target +
        |finitePositiveWeightExpectation leftWeight
            (finitePositiveWeightRandomScanConditionalExpectation
              rightWeight f) -
          finitePositiveWeightExpectation rightWeight
            (finitePositiveWeightRandomScanConditionalExpectation
              rightWeight f)| := by
  let leftScan :=
    finitePositiveWeightRandomScanConditionalExpectation leftWeight f
  let rightScan :=
    finitePositiveWeightRandomScanConditionalExpectation rightWeight f
  let sourceError :=
    (Fintype.card ι : ℝ)⁻¹ *
      ∑ target : ι, sourceBound target * P.variation target
  have hSourceErrorNonneg : 0 ≤ sourceError := by
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun target _htarget =>
        mul_nonneg (hSourceBound target) (P.variation_nonneg target))
  have hPointwise (A : ι → G) :
      |leftScan A - rightScan A| ≤ sourceError := by
    exact
      P.randomScan_crossWeight_difference_abs_le_sourcePairing
        leftWeight rightWeight hLeftWeight hRightWeight
        sourceBound hCrossL1 A
  have hMean :
      |finitePositiveWeightExpectation leftWeight (leftScan - rightScan)| ≤
        sourceError := by
    apply finitePositiveWeightExpectation_abs_le_of_pointwise
      leftWeight hLeftWeight (leftScan - rightScan)
      sourceError hSourceErrorNonneg
    intro A
    simpa [leftScan, rightScan] using hPointwise A
  have hStationaryLeft :=
    finitePositiveWeightExpectation_randomScan_eq
      leftWeight hLeftWeight f
  have hStationaryRight :=
    finitePositiveWeightExpectation_randomScan_eq
      rightWeight hRightWeight f
  have hSplit :
      finitePositiveWeightExpectation leftWeight leftScan -
          finitePositiveWeightExpectation rightWeight rightScan =
        finitePositiveWeightExpectation leftWeight (leftScan - rightScan) +
          (finitePositiveWeightExpectation leftWeight rightScan -
            finitePositiveWeightExpectation rightWeight rightScan) := by
    rw [finitePositiveWeightExpectation_sub]
    ring
  rw [← hStationaryLeft, ← hStationaryRight, hSplit]
  exact le_trans (abs_add_le _ _)
    (add_le_add hMean (le_refl _))

end

end MathlibAnalytic
end MGAP4D
