import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCrossBoundaryHeatBathRow
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance referenceCrossBoundaryInfluenceOperatorSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The single surviving C5 cross-boundary bounded-test influence coefficient. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
    (beta : ℝ) : ℝ :=
  2 *
    (((Real.exp (8 * beta)) ^ 2 - 1) /
      ((Real.exp (8 * beta)) ^ 2 + 1))

/-- The finite cross-boundary influence operator acting on a source variation
profile.  The row kernel is the exact support majorant from the previous unit. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryInfluenceOperator
    (H : ℕ)
    (beta : ℝ)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (fiber : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
        beta fiber source * variation source

/-- Exact diagonal support makes the finite cross-boundary influence operator
identically equal to scalar multiplication by the single surviving coefficient.
There is no spatial-volume factor. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryInfluenceOperator_eq_coefficient_mul
    (H : ℕ)
    (beta : ℝ)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (fiber : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryInfluenceOperator
        H beta variation fiber =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
        beta * variation fiber := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryInfluenceOperator
  rw [Finset.sum_eq_single fiber]
  · simp [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient]
  · intro source _hsource hne
    simp [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant,
      hne]
  · simp

/-- The scalar C5 cross-boundary contraction coefficient is nonnegative at
nonnegative coupling. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient_nonneg
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
        beta := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
  have hExpOne : (1 : ℝ) ≤ Real.exp (8 * beta) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hNum : 0 ≤ (Real.exp (8 * beta)) ^ 2 - 1 := by
    calc
      0 ≤
          (Real.exp (8 * beta) - 1) *
            (Real.exp (8 * beta) + 1) :=
        mul_nonneg (sub_nonneg.mpr hExpOne) (by positivity)
      _ = (Real.exp (8 * beta)) ^ 2 - 1 := by ring
  have hDen : 0 ≤ (Real.exp (8 * beta)) ^ 2 + 1 := by
    positivity
  exact mul_nonneg (by norm_num) (div_nonneg hNum hDen)

/-- The existing explicit small-coupling diagonal estimate is exactly an
estimate on the named scalar cross-boundary contraction coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient_lt_one_of_beta_lt
    (beta : ℝ)
    (hBetaLt :
      beta <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBetaThreshold) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
        beta < 1 := by
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient] using
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundary_diagonalCoefficient_lt_one_of_beta_lt
      beta hBetaLt

/-- RED theorem for the bounded-profile pointwise operator contraction. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryInfluenceOperator_abs_le_coefficient_mul
    (H : ℕ)
    (beta M : ℝ)
    (hbeta : 0 ≤ beta)
    (hM : 0 ≤ M)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hvariation : ∀ source, |variation source| ≤ M)
    (fiber : PeriodicHypercubicEvenSpatialSliceLink H) :
    |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryInfluenceOperator
        H beta variation fiber| ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
        beta * M := by
  rfl

end

end MathlibAnalytic
end MGAP4D
