import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2UnitMass

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Finite-support norm-squared bridge for the concrete unit vector.  This is a
norm-squared bridge over the singleton support, not yet the Mathlib Hilbert norm
on a completed `l2` Hilbert space. -/
def concreteL2UnitFiniteSupportNormSq (k : ℕ) : ℝ :=
  concreteL2UnitSingletonSquaredMass k

/-- The finite-support norm-squared bridge of the concrete unit vector is one. -/
theorem concrete_l2_unit_finite_support_norm_sq_eq_one (k : ℕ) :
    concreteL2UnitFiniteSupportNormSq k = 1 := by
  exact concrete_l2_unit_singleton_squared_mass_eq_one k

/-- Surface recording the bridge from coordinate unit mass to finite-support
norm-squared normalization.  This is not yet a completed Hilbert norm theorem,
not graph-norm completion, not operator-norm unboundedness, not graph closure,
not a closed-operator theorem, and not self-adjointness. -/
structure ConcreteL2UnitNormSquaredBridgeSurface where
  unitMassReady : concreteAnalyticSpineL2UnitMassSurfaceReady
  finiteSupportNormSq : ℕ → ℝ
  finiteSupportNormSqEqOne : ∀ k : ℕ, finiteSupportNormSq k = 1
  boundaryNotCompletedHilbertNormTheorem : Prop
  boundaryNotGraphNormCompletion : Prop
  boundaryNotOperatorNormUnboundednessTheorem : Prop
  boundaryNotGraphClosure : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop

/-- The concrete finite-support norm-squared bridge surface. -/
def concreteL2UnitNormSquaredBridgeSurface :
    ConcreteL2UnitNormSquaredBridgeSurface :=
  { unitMassReady := concrete_analytic_spine_l2_unit_mass_surface_ready
    finiteSupportNormSq := concreteL2UnitFiniteSupportNormSq
    finiteSupportNormSqEqOne := concrete_l2_unit_finite_support_norm_sq_eq_one
    boundaryNotCompletedHilbertNormTheorem := True
    boundaryNotGraphNormCompletion := True
    boundaryNotOperatorNormUnboundednessTheorem := True
    boundaryNotGraphClosure := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True }

/-- Readiness for the concrete finite-support norm-squared bridge. -/
def concreteAnalyticSpineL2UnitNormSquaredBridgeSurfaceReady : Prop :=
  concreteAnalyticSpineL2UnitMassSurfaceReady ∧
  (∀ k : ℕ, concreteL2UnitFiniteSupportNormSq k = 1) ∧
  concreteL2UnitNormSquaredBridgeSurface.boundaryNotCompletedHilbertNormTheorem ∧
  concreteL2UnitNormSquaredBridgeSurface.boundaryNotGraphNormCompletion ∧
  concreteL2UnitNormSquaredBridgeSurface.boundaryNotOperatorNormUnboundednessTheorem ∧
  concreteL2UnitNormSquaredBridgeSurface.boundaryNotGraphClosure ∧
  concreteL2UnitNormSquaredBridgeSurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2UnitNormSquaredBridgeSurface.boundaryNotSelfAdjointness

/-- Readiness theorem for the concrete finite-support norm-squared bridge. -/
theorem concrete_analytic_spine_l2_unit_norm_squared_bridge_surface_ready :
    concreteAnalyticSpineL2UnitNormSquaredBridgeSurfaceReady := by
  unfold concreteAnalyticSpineL2UnitNormSquaredBridgeSurfaceReady
  exact And.intro concrete_analytic_spine_l2_unit_mass_surface_ready <|
    And.intro concrete_l2_unit_finite_support_norm_sq_eq_one <|
      And.intro trivial <| And.intro trivial <| And.intro trivial <|
        And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the concrete finite-support norm-squared bridge. -/
def concreteAnalyticSpineL2UnitNormSquaredBridgeHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2UnitNormSquaredBridgeSurfaceReady

/-- Boundary theorem for the concrete finite-support norm-squared bridge. -/
theorem concrete_analytic_spine_l2_unit_norm_squared_bridge_hard_residual_boundary_held :
    concreteAnalyticSpineL2UnitNormSquaredBridgeHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_unit_norm_squared_bridge_surface_ready

end

end MathlibAnalytic
end MGAP4D
