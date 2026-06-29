import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonHeatBathHamiltonianL2
import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonHeatBathVacuumL2

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Remove the normalized Gibbs-vacuum component from an arbitrary Gibbs
`L²` vector. -/
def ContinuousCompactOrientedGaugeWilsonSystem.vacuumCenteredL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure) : Lp ℝ 2 C.gibbsMeasure :=
  f - inner ℝ C.gibbsVacuumL2 f • C.gibbsVacuumL2

/-- Abstract finite-volume Poincaré inequality for the native compact-group
orientation-correct heat-bath Hamiltonian. -/
def ContinuousCompactOrientedGaugeWilsonSystem.HeatBathPoincareL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (gap : ℝ) : Prop :=
  ∀ f : Lp ℝ 2 C.gibbsMeasure,
    gap * ‖C.vacuumCenteredL2 f‖ ^ 2 ≤
      inner ℝ (C.heatBathHamiltonianL2 f) f

/-- The orthogonal complement of the normalized Gibbs-vacuum line. -/
def ContinuousCompactOrientedGaugeWilsonSystem.VacuumOrthogonalL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    Submodule ℝ (Lp ℝ 2 C.gibbsMeasure) :=
  (Submodule.span ℝ {C.gibbsVacuumL2}).orthogonal

/-- Membership in the vacuum-orthogonal sector is exactly vanishing inner
product with the normalized Gibbs vacuum. -/
theorem continuous_compact_oriented_mem_vacuumOrthogonalL2_iff
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    f ∈ C.VacuumOrthogonalL2 ↔ inner ℝ C.gibbsVacuumL2 f = 0 := by
  exact Submodule.mem_orthogonal_singleton_iff_inner_right

/-- Vacuum centering fixes every vector orthogonal to the normalized Gibbs
vacuum. -/
theorem continuous_compact_oriented_vacuumCenteredL2_eq_self
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure)
    (hf : inner ℝ C.gibbsVacuumL2 f = 0) :
    C.vacuumCenteredL2 f = f := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.vacuumCenteredL2
  rw [hf]
  simp

/-- Any native compact heat-bath Poincaré inequality gives the corresponding
Hamiltonian coercivity bound on the Gibbs-vacuum orthogonal sector. -/
theorem continuous_compact_oriented_heatBathHamiltonianL2_gap_on_vacuumOrthogonal
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (gap : ℝ)
    (hPoincare : C.HeatBathPoincareL2 gap)
    (f : Lp ℝ 2 C.gibbsMeasure)
    (hf : inner ℝ C.gibbsVacuumL2 f = 0) :
    gap * ‖f‖ ^ 2 ≤
      inner ℝ (C.heatBathHamiltonianL2 f) f := by
  simpa [continuous_compact_oriented_vacuumCenteredL2_eq_self C f hf] using
    hPoincare f

/-- A strictly positive compact heat-bath Poincaré constant excludes nonzero
zero-energy vectors in the vacuum-orthogonal sector. -/
theorem continuous_compact_oriented_heatBathHamiltonianL2_kernel_eq_vacuum_on_orthogonal
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (gap : ℝ)
    (hgap : 0 < gap)
    (hPoincare : C.HeatBathPoincareL2 gap)
    (f : Lp ℝ 2 C.gibbsMeasure)
    (hfOrth : inner ℝ C.gibbsVacuumL2 f = 0)
    (hfZero : C.heatBathHamiltonianL2 f = 0) :
    f = 0 := by
  have hcoercive :=
    continuous_compact_oriented_heatBathHamiltonianL2_gap_on_vacuumOrthogonal
      C gap hPoincare f hfOrth
  rw [hfZero, inner_zero_left] at hcoercive
  have hnormsq : ‖f‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖f‖]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnormsq)

end

end MathlibAnalytic
end MGAP4D
