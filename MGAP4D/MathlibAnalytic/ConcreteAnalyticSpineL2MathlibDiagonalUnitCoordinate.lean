import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2UnitNormTransport

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- Coordinatewise diagonal action on a Mathlib-side coordinate unit. -/
def concreteL2MathlibDiagonalUnitCoordinateAction (k n : ℕ) : ℝ :=
  concreteL2DiagonalWeight n * concreteL2MathlibUnit k n

/-- At the selected coordinate, the Mathlib-side unit sees the diagonal weight. -/
theorem concrete_l2_mathlib_diagonal_unit_coordinate_action_self (k : ℕ) :
    concreteL2MathlibDiagonalUnitCoordinateAction k k = concreteL2DiagonalWeight k := by
  simp [concreteL2MathlibDiagonalUnitCoordinateAction]

/-- Away from the selected coordinate, the Mathlib-side coordinate action vanishes. -/
theorem concrete_l2_mathlib_diagonal_unit_coordinate_action_off (k n : ℕ) (h : n ≠ k) :
    concreteL2MathlibDiagonalUnitCoordinateAction k n = 0 := by
  simp [concreteL2MathlibDiagonalUnitCoordinateAction, concrete_l2_mathlib_unit_apply_ne h]

/-- Coordinate identity for the Mathlib-side unit action. -/
theorem concrete_l2_mathlib_diagonal_unit_coordinate_law (k n : ℕ) :
    concreteL2MathlibDiagonalUnitCoordinateAction k n =
      concreteL2DiagonalWeight k * concreteL2MathlibUnit k n := by
  by_cases h : n = k
  · subst h
    simp [concreteL2MathlibDiagonalUnitCoordinateAction]
  · simp [concreteL2MathlibDiagonalUnitCoordinateAction, concrete_l2_mathlib_unit_apply_ne h]

/-- Readiness for the Mathlib diagonal unit coordinate lane. -/
def concreteAnalyticSpineL2MathlibDiagonalUnitCoordinateReady : Prop :=
  concreteAnalyticSpineL2UnitNormTransportSurfaceReady ∧
  (∀ k n : ℕ,
    concreteL2MathlibDiagonalUnitCoordinateAction k n =
      concreteL2DiagonalWeight k * concreteL2MathlibUnit k n)

/-- The Mathlib diagonal unit coordinate lane is ready. -/
theorem concrete_analytic_spine_l2_mathlib_diagonal_unit_coordinate_ready :
    concreteAnalyticSpineL2MathlibDiagonalUnitCoordinateReady := by
  exact And.intro
    concrete_analytic_spine_l2_unit_norm_transport_surface_ready
    concrete_l2_mathlib_diagonal_unit_coordinate_law

end

end MathlibAnalytic
end MGAP4D
