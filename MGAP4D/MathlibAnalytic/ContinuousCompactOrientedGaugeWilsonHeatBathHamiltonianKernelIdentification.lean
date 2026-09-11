import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonHeatBathPoincareL2

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- A positive compact heat-bath Poincaré constant makes every zero-energy
vector a canonical multiple of the normalized Gibbs vacuum. -/
theorem continuous_compact_oriented_heatBathHamiltonianL2_eq_inner_smul_vacuum_of_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (gap : ℝ)
    (hgap : 0 < gap)
    (hPoincare : C.HeatBathPoincareL2 gap)
    (f : Lp ℝ 2 C.gibbsMeasure)
    (hfZero : C.heatBathHamiltonianL2 f = 0) :
    f = inner ℝ C.gibbsVacuumL2 f • C.gibbsVacuumL2 := by
  have hbound := hPoincare f
  rw [hfZero, inner_zero_left] at hbound
  have hnonneg :
      0 ≤ gap * ‖C.vacuumCenteredL2 f‖ ^ 2 :=
    mul_nonneg hgap.le (sq_nonneg _)
  have hproductZero :
      gap * ‖C.vacuumCenteredL2 f‖ ^ 2 = 0 :=
    le_antisymm hbound hnonneg
  have hnormSq : ‖C.vacuumCenteredL2 f‖ ^ 2 = 0 :=
    (mul_eq_zero.mp hproductZero).resolve_left (ne_of_gt hgap)
  have hnorm : ‖C.vacuumCenteredL2 f‖ = 0 := by
    nlinarith [norm_nonneg (C.vacuumCenteredL2 f)]
  have hcenteredZero : C.vacuumCenteredL2 f = 0 :=
    norm_eq_zero.mp hnorm
  have hsub :
      f - inner ℝ C.gibbsVacuumL2 f • C.gibbsVacuumL2 = 0 := by
    simpa only [ContinuousCompactOrientedGaugeWilsonSystem.vacuumCenteredL2] using
      hcenteredZero
  exact sub_eq_zero.mp hsub

/-- Under a positive compact heat-bath Poincaré inequality, the zero eigenspace
of the native finite-volume Hamiltonian is exactly the normalized Gibbs-vacuum
line. -/
theorem continuous_compact_oriented_heatBathHamiltonianL2_eq_zero_iff_eq_inner_smul_vacuum
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (gap : ℝ)
    (hgap : 0 < gap)
    (hPoincare : C.HeatBathPoincareL2 gap)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.heatBathHamiltonianL2 f = 0 ↔
      f = inner ℝ C.gibbsVacuumL2 f • C.gibbsVacuumL2 := by
  constructor
  · exact
      continuous_compact_oriented_heatBathHamiltonianL2_eq_inner_smul_vacuum_of_eq_zero
        C gap hgap hPoincare f
  · intro hf
    rw [hf]
    calc
      C.heatBathHamiltonianL2
          (inner ℝ C.gibbsVacuumL2 f • C.gibbsVacuumL2) =
          inner ℝ C.gibbsVacuumL2 f •
            C.heatBathHamiltonianL2 C.gibbsVacuumL2 := by
        exact C.heatBathHamiltonianL2.map_smul
          (inner ℝ C.gibbsVacuumL2 f) C.gibbsVacuumL2
      _ = 0 := by
        rw [continuous_compact_oriented_heatBathHamiltonianL2_vacuum,
          smul_zero]

end

end MathlibAnalytic
end MGAP4D
