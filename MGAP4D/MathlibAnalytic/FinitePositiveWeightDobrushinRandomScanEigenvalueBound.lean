import MGAP4D.MathlibAnalytic.FinitePositiveWeightCanonicalVariationDefiniteness
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The canonical total coordinate variation of the generic positive-weight
random-scan operator contracts at the standard Dobrushin rate. -/
theorem finitePositiveWeightRandomScan_canonicalTotalVariation_le_rate_mul
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (f : (ι → G) → ℝ)
    (D : FinitePositiveWeightDobrushinL1MatrixData weight)
    (hCard : 0 < Fintype.card ι) :
    finiteProductCanonicalTotalVariation
        (finitePositiveWeightRandomScanConditionalExpectation weight f) ≤
      finitePositiveWeightDobrushinRandomScanRate D *
        finiteProductCanonicalTotalVariation f := by
  let P := finiteProductCanonicalVariationBound f
  let Q := P.randomScanVariationBound hweight D
  have hCanonical :
      finiteProductCanonicalTotalVariation
          (finitePositiveWeightRandomScanConditionalExpectation weight f) ≤
        finiteProductVariationTotal Q.variation := by
    unfold finiteProductCanonicalTotalVariation finiteProductVariationTotal
    apply Finset.sum_le_sum
    intro e _he
    exact finiteProductCanonicalVariation_le_variationBound Q e
  have hDeclared := P.randomScan_totalVariation_le_rate_mul hweight D hCard
  calc
    finiteProductCanonicalTotalVariation
        (finitePositiveWeightRandomScanConditionalExpectation weight f) ≤
      finiteProductVariationTotal Q.variation := hCanonical
    _ ≤ finitePositiveWeightDobrushinRandomScanRate D *
        finiteProductVariationTotal P.variation := hDeclared
    _ = finitePositiveWeightDobrushinRandomScanRate D *
        finiteProductCanonicalTotalVariation f := by
      rfl

/-- Every nonconstant eigenobservable of the generic positive-weight
random-scan conditional expectation operator has eigenvalue bounded in modulus
by the Dobrushin random-scan rate. -/
theorem finitePositiveWeightRandomScan_eigenvalue_abs_le_rate
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (f : (ι → G) → ℝ)
    (D : FinitePositiveWeightDobrushinL1MatrixData weight)
    (hCard : 0 < Fintype.card ι)
    (eigenvalue : ℝ)
    (hEigen :
      finitePositiveWeightRandomScanConditionalExpectation weight f =
        eigenvalue • f)
    (hVariation : finiteProductCanonicalTotalVariation f ≠ 0) :
    |eigenvalue| ≤ finitePositiveWeightDobrushinRandomScanRate D := by
  have hContract :=
    finitePositiveWeightRandomScan_canonicalTotalVariation_le_rate_mul
      weight hweight f D hCard
  rw [hEigen, finiteProductCanonicalTotalVariation_smul] at hContract
  have hVariationPos : 0 < finiteProductCanonicalTotalVariation f :=
    lt_of_le_of_ne
      (finiteProductCanonicalTotalVariation_nonneg f)
      (Ne.symm hVariation)
  nlinarith

/-- Every nonzero positive-weight-centered eigenobservable has eigenvalue
bounded in modulus by the same strict Dobrushin rate. -/
theorem finitePositiveWeight_centered_randomScan_eigenvalue_abs_le_rate
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (f : (ι → G) → ℝ)
    (D : FinitePositiveWeightDobrushinL1MatrixData weight)
    (hCard : 0 < Fintype.card ι)
    (eigenvalue : ℝ)
    (hCenter : finitePositiveWeightSum weight f = 0)
    (hNonzero : f ≠ 0)
    (hEigen :
      finitePositiveWeightRandomScanConditionalExpectation weight f =
        eigenvalue • f) :
    |eigenvalue| ≤ finitePositiveWeightDobrushinRandomScanRate D := by
  exact finitePositiveWeightRandomScan_eigenvalue_abs_le_rate
    weight hweight f D hCard eigenvalue hEigen
    (finitePositiveWeight_centered_canonicalTotalVariation_ne_zero
      weight hweight f hCenter hNonzero)

/-- In particular every nonzero centered eigenobservable has eigenvalue
strictly below one. -/
theorem finitePositiveWeight_centered_randomScan_eigenvalue_lt_one
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (f : (ι → G) → ℝ)
    (D : FinitePositiveWeightDobrushinL1MatrixData weight)
    (hCard : 0 < Fintype.card ι)
    (eigenvalue : ℝ)
    (hCenter : finitePositiveWeightSum weight f = 0)
    (hNonzero : f ≠ 0)
    (hEigen :
      finitePositiveWeightRandomScanConditionalExpectation weight f =
        eigenvalue • f) :
    eigenvalue < 1 := by
  have hAbs :=
    finitePositiveWeight_centered_randomScan_eigenvalue_abs_le_rate
      weight hweight f D hCard eigenvalue hCenter hNonzero hEigen
  exact lt_of_le_of_lt (le_trans (le_abs_self eigenvalue) hAbs)
    (finitePositiveWeightDobrushinRandomScanRate_lt_one D hCard)

end

end MathlibAnalytic
end MGAP4D
