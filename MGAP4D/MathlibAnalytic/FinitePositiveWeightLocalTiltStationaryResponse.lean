import MGAP4D.MathlibAnalytic.FinitePositiveWeightStationaryRandomScanComparisonGeometricResidual
import MGAP4D.MathlibAnalytic.FinitePositiveWeightLocalTiltConditional
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A bounded positive finite-support multiplicative tilt canonically produces
stationary cross-weight comparison data, with the untilted positive weight as
the right/reference Gibbs specification. -/
def finitePositiveWeightLocalTiltStationaryComparisonData
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight tilt : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (htilt : ∀ A : ι → G, 0 < tilt A)
    (support : Finset ι)
    (htiltSupport : FiniteProductFunctionSupportedOn support tilt)
    (lower upper : ℝ)
    (hLower : 0 < lower)
    (hUpper : 0 < upper)
    (hLowerUpper : lower ≤ upper)
    (htiltLower : ∀ A : ι → G, lower ≤ tilt A)
    (htiltUpper : ∀ A : ι → G, tilt A ≤ upper)
    (hCard : 0 < Fintype.card ι)
    (D : FinitePositiveWeightDobrushinL1MatrixData weight) :
    FinitePositiveWeightStationaryRandomScanComparisonData
      (finitePositiveWeightMultiplicativeTilt weight tilt) weight :=
  { leftWeight_pos :=
      finitePositiveWeightMultiplicativeTilt_pos weight tilt hweight htilt
    rightWeight_pos := hweight
    coordinateCard_pos := hCard
    sourceBound :=
      finitePositiveWeightLocalTiltConditionalSourceBound
        support lower upper
    conditionalCrossL1_le_sourceBound := by
      intro A target
      exact
        finitePositiveWeightMultiplicativeTilt_singleSiteConditionalCrossL1_le_sourceBound
          weight tilt hweight htilt support htiltSupport
          lower upper hLower hUpper hLowerUpper
          htiltLower htiltUpper A target
    rightDobrushin := D }

/-- The stationary expectation response to a bounded finite-support local tilt
is controlled by its exact accumulated source pairing and the geometric
right-weight Dobrushin terminal residual. -/
theorem finitePositiveWeightLocalTilt_globalExpectation_discrepancy_le
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight tilt : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (htilt : ∀ A : ι → G, 0 < tilt A)
    (support : Finset ι)
    (htiltSupport : FiniteProductFunctionSupportedOn support tilt)
    (lower upper : ℝ)
    (hLower : 0 < lower)
    (hUpper : 0 < upper)
    (hLowerUpper : lower ≤ upper)
    (htiltLower : ∀ A : ι → G, lower ≤ tilt A)
    (htiltUpper : ∀ A : ι → G, tilt A ≤ upper)
    (hCard : 0 < Fintype.card ι)
    (D : FinitePositiveWeightDobrushinL1MatrixData weight)
    {f : (ι → G) → ℝ}
    (P : FiniteProductVariationBound f)
    (n : ℕ) :
    |finitePositiveWeightGlobalExpectation
          (finitePositiveWeightMultiplicativeTilt weight tilt) f -
        finitePositiveWeightGlobalExpectation weight f| ≤
      FinitePositiveWeightStationaryRandomScanComparisonData.partialStationarySource
          P
          (finitePositiveWeightLocalTiltStationaryComparisonData
            weight tilt hweight htilt support htiltSupport
            lower upper hLower hUpper hLowerUpper
            htiltLower htiltUpper hCard D)
          n +
        2 * finitePositiveWeightDobrushinRandomScanRate D ^ n *
          finiteProductVariationTotal P.variation := by
  let C := finitePositiveWeightLocalTiltStationaryComparisonData
    weight tilt hweight htilt support htiltSupport
    lower upper hLower hUpper hLowerUpper
    htiltLower htiltUpper hCard D
  exact
    C.expectationDiscrepancy_le_partialSource_add_geometricResidual P n

/-- A uniform pointwise lower bound on an observable is inherited by every
normalized global expectation of a positive finite product weight. -/
theorem finitePositiveWeightGlobalExpectation_lower
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (f : (ι → G) → ℝ)
    (lower : ℝ)
    (hLower : ∀ A : ι → G, lower ≤ f A) :
    lower ≤ finitePositiveWeightGlobalExpectation weight f := by
  unfold finitePositiveWeightGlobalExpectation
  calc
    lower =
        ∑ A : ι → G,
          finitePositiveWeightGlobalProbability weight A * lower := by
      rw [← Finset.sum_mul,
        finitePositiveWeightGlobalProbability_sum_eq_one weight hweight,
        one_mul]
    _ ≤ ∑ A : ι → G,
        finitePositiveWeightGlobalProbability weight A * f A := by
      apply Finset.sum_le_sum
      intro A _hA
      exact mul_le_mul_of_nonneg_left
        (hLower A)
        (finitePositiveWeightGlobalProbability_nonneg weight hweight A)

/-- An absolute expectation discrepancy plus a positive lower bound for the
reference expectation gives a one-sided multiplicative response bound. -/
theorem finitePositiveWeightGlobalExpectation_le_one_add_error_div_lower_mul
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (leftWeight rightWeight : (ι → G) → ℝ)
    (hRightWeight : ∀ A : ι → G, 0 < rightWeight A)
    (f : (ι → G) → ℝ)
    (lower error : ℝ)
    (hLowerPos : 0 < lower)
    (hfLower : ∀ A : ι → G, lower ≤ f A)
    (hErrorNonneg : 0 ≤ error)
    (hDiscrepancy :
      |finitePositiveWeightGlobalExpectation leftWeight f -
          finitePositiveWeightGlobalExpectation rightWeight f| ≤ error) :
    finitePositiveWeightGlobalExpectation leftWeight f ≤
      (1 + error / lower) *
        finitePositiveWeightGlobalExpectation rightWeight f := by
  have hReferenceLower :
      lower ≤ finitePositiveWeightGlobalExpectation rightWeight f :=
    finitePositiveWeightGlobalExpectation_lower
      rightWeight hRightWeight f lower hfLower
  have hReferencePos :
      0 < finitePositiveWeightGlobalExpectation rightWeight f :=
    lt_of_lt_of_le hLowerPos hReferenceLower
  have hAdd :
      finitePositiveWeightGlobalExpectation leftWeight f ≤
        finitePositiveWeightGlobalExpectation rightWeight f + error := by
    have hUpper := (abs_le.mp (hDiscrepancy.trans (le_refl error))).2
    linarith
  have hScale :
      error ≤ (error / lower) *
        finitePositiveWeightGlobalExpectation rightWeight f := by
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hLowerPos).2
      (by
        have := mul_le_mul_of_nonneg_left hReferenceLower hErrorNonneg
        simpa [mul_comm, mul_left_comm, mul_assoc] using this)
  calc
    finitePositiveWeightGlobalExpectation leftWeight f ≤
        finitePositiveWeightGlobalExpectation rightWeight f + error := hAdd
    _ ≤ finitePositiveWeightGlobalExpectation rightWeight f +
        (error / lower) *
          finitePositiveWeightGlobalExpectation rightWeight f :=
      add_le_add_left hScale _
    _ = (1 + error / lower) *
        finitePositiveWeightGlobalExpectation rightWeight f := by ring

end

end MathlibAnalytic
end MGAP4D
