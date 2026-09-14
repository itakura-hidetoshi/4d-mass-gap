import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCrossBoundaryDiagonalInfluence
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section

local instance referenceCrossBoundaryRowSumSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The exact C5 cross-boundary bounded-test majorant after the support theorem:
all off-diagonal sources vanish, and only the source matching the resampled
left fiber carries the diagonal Harnack coefficient. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
    {H : ℕ}
    (beta : ℝ)
    (fiber source : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  if source = fiber then
    2 *
      (((Real.exp (8 * beta)) ^ 2 - 1) /
        ((Real.exp (8 * beta)) ^ 2 + 1))
  else 0

/-- The corresponding finite source row sum. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorantRowSum
    (H : ℕ)
    (beta : ℝ)
    (fiber : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
      beta fiber source

/-- RED probe: after off-diagonal cancellation the entire source row should
collapse to the single diagonal coefficient, with no volume cardinality. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorantRowSum_eq_diagonal
    (H : ℕ)
    (beta : ℝ)
    (fiber : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorantRowSum
        H beta fiber =
      2 *
        (((Real.exp (8 * beta)) ^ 2 - 1) /
          ((Real.exp (8 * beta)) ^ 2 + 1)) := by
  rfl

end

end MathlibAnalytic
end MGAP4D
