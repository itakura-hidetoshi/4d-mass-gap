import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonRandomScanSpectralEnclosureL2

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The heat-bath Hamiltonian takes values in the Gibbs-vacuum orthogonal sector. -/
theorem continuous_compact_oriented_heatBathHamiltonianL2_mem_vacuumOrthogonal
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.heatBathHamiltonianL2 f ∈ C.VacuumOrthogonalL2 := by
  rw [continuous_compact_oriented_mem_vacuumOrthogonalL2_iff]
  calc
    inner ℝ C.gibbsVacuumL2 (C.heatBathHamiltonianL2 f) =
        inner ℝ (C.heatBathHamiltonianL2 C.gibbsVacuumL2) f := by
      symm
      exact continuous_compact_oriented_heatBathHamiltonianL2_inner_symm
        C C.gibbsVacuumL2 f
    _ = 0 := by
      rw [continuous_compact_oriented_heatBathHamiltonianL2_vacuum,
        inner_zero_left]

/-- Algebraic restriction of random scan to the vacuum-orthogonal sector. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.randomScanVacuumOrthogonalLinearMap
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge) :
    C.VacuumOrthogonalL2 →ₗ[ℝ] C.VacuumOrthogonalL2 :=
  C.randomScanHeatBathL2.toLinearMap.restrict fun f hf =>
    continuous_compact_oriented_randomScanHeatBathL2_mem_vacuumOrthogonal
      C hEdge f hf

/-- Algebraic restriction of the Hamiltonian to the vacuum-orthogonal sector. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.heatBathHamiltonianVacuumOrthogonalLinearMap
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    C.VacuumOrthogonalL2 →ₗ[ℝ] C.VacuumOrthogonalL2 :=
  C.heatBathHamiltonianL2.toLinearMap.restrict fun f _ =>
    continuous_compact_oriented_heatBathHamiltonianL2_mem_vacuumOrthogonal C f

/-- Continuous random scan on the vacuum-orthogonal Hilbert sector. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.randomScanVacuumOrthogonalL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge) :
    C.VacuumOrthogonalL2 →L[ℝ] C.VacuumOrthogonalL2 :=
  (C.randomScanVacuumOrthogonalLinearMap hEdge).mkContinuous
    ‖C.randomScanHeatBathL2‖ fun f => by
      change
        ‖C.randomScanHeatBathL2 (f : Lp ℝ 2 C.gibbsMeasure)‖ ≤
          ‖C.randomScanHeatBathL2‖ * ‖(f : Lp ℝ 2 C.gibbsMeasure)‖
      exact C.randomScanHeatBathL2.le_opNorm _

/-- Continuous Hamiltonian on the vacuum-orthogonal Hilbert sector. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.heatBathHamiltonianVacuumOrthogonalL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    C.VacuumOrthogonalL2 →L[ℝ] C.VacuumOrthogonalL2 :=
  C.heatBathHamiltonianVacuumOrthogonalLinearMap.mkContinuous
    ‖C.heatBathHamiltonianL2‖ fun f => by
      change
        ‖C.heatBathHamiltonianL2 (f : Lp ℝ 2 C.gibbsMeasure)‖ ≤
          ‖C.heatBathHamiltonianL2‖ * ‖(f : Lp ℝ 2 C.gibbsMeasure)‖
      exact C.heatBathHamiltonianL2.le_opNorm _

@[simp] theorem continuous_compact_oriented_randomScanVacuumOrthogonalL2_coe_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge)
    (f : C.VacuumOrthogonalL2) :
    ((C.randomScanVacuumOrthogonalL2 hEdge f : C.VacuumOrthogonalL2) :
        Lp ℝ 2 C.gibbsMeasure) =
      C.randomScanHeatBathL2 (f : Lp ℝ 2 C.gibbsMeasure) := rfl

@[simp] theorem continuous_compact_oriented_heatBathHamiltonianVacuumOrthogonalL2_coe_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : C.VacuumOrthogonalL2) :
    ((C.heatBathHamiltonianVacuumOrthogonalL2 f : C.VacuumOrthogonalL2) :
        Lp ℝ 2 C.gibbsMeasure) =
      C.heatBathHamiltonianL2 (f : Lp ℝ 2 C.gibbsMeasure) := rfl

end

end MathlibAnalytic
end MGAP4D
