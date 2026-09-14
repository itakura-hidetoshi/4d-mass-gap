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

end

end MathlibAnalytic
end MGAP4D
