import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonVacuumOrthogonalOperatorCoreL2

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Restricted random scan is symmetric on the vacuum-orthogonal sector. -/
theorem continuous_compact_oriented_randomScanVacuumOrthogonalL2_inner_symm
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge)
    (f g : C.VacuumOrthogonalL2) :
    inner ℝ (C.randomScanVacuumOrthogonalL2 hEdge f) g =
      inner ℝ f (C.randomScanVacuumOrthogonalL2 hEdge g) := by
  change
    inner ℝ (C.randomScanHeatBathL2 (f : Lp ℝ 2 C.gibbsMeasure))
        (g : Lp ℝ 2 C.gibbsMeasure) =
      inner ℝ (f : Lp ℝ 2 C.gibbsMeasure)
        (C.randomScanHeatBathL2 (g : Lp ℝ 2 C.gibbsMeasure))
  exact continuous_compact_oriented_randomScanHeatBathL2_inner_symm C _ _

end

end MathlibAnalytic
end MGAP4D
