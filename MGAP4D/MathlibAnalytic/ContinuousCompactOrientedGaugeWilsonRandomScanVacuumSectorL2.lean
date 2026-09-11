import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathRandomScanOperatorL2

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Self-adjoint random scan preserves the orthogonal complement of the
normalized Gibbs-vacuum line. -/
theorem continuous_compact_oriented_randomScanHeatBathL2_mem_vacuumOrthogonal
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge)
    (f : Lp ℝ 2 C.gibbsMeasure)
    (hf : f ∈ C.VacuumOrthogonalL2) :
    C.randomScanHeatBathL2 f ∈ C.VacuumOrthogonalL2 := by
  rw [continuous_compact_oriented_mem_vacuumOrthogonalL2_iff] at hf ⊢
  calc
    inner ℝ C.gibbsVacuumL2 (C.randomScanHeatBathL2 f) =
        inner ℝ (C.randomScanHeatBathL2 C.gibbsVacuumL2) f := by
      symm
      exact continuous_compact_oriented_randomScanHeatBathL2_inner_symm
        C C.gibbsVacuumL2 f
    _ = inner ℝ C.gibbsVacuumL2 f := by
      rw [continuous_compact_oriented_randomScanHeatBathL2_vacuum C hEdge]
    _ = 0 := hf

/-- Random scan commutes with removal of the normalized Gibbs-vacuum
component. -/
theorem continuous_compact_oriented_randomScanHeatBathL2_vacuumCentered
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.randomScanHeatBathL2 (C.vacuumCenteredL2 f) =
      C.vacuumCenteredL2 (C.randomScanHeatBathL2 f) := by
  have hInner :
      inner ℝ C.gibbsVacuumL2 (C.randomScanHeatBathL2 f) =
        inner ℝ C.gibbsVacuumL2 f := by
    calc
      inner ℝ C.gibbsVacuumL2 (C.randomScanHeatBathL2 f) =
          inner ℝ (C.randomScanHeatBathL2 C.gibbsVacuumL2) f := by
        symm
        exact continuous_compact_oriented_randomScanHeatBathL2_inner_symm
          C C.gibbsVacuumL2 f
      _ = inner ℝ C.gibbsVacuumL2 f := by
        rw [continuous_compact_oriented_randomScanHeatBathL2_vacuum C hEdge]
  unfold ContinuousCompactOrientedGaugeWilsonSystem.vacuumCenteredL2
  rw [map_sub, map_smul,
    continuous_compact_oriented_randomScanHeatBathL2_vacuum C hEdge,
    hInner]

end

end MathlibAnalytic
end MGAP4D
