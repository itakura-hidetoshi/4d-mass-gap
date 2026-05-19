import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2UnitProbe

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The obstruction witness also selects a concrete unit probe. -/
def concreteL2ObstructionUnitProbe (k : ℕ) : ConcreteL2RealSequence :=
  concreteL2Unit (concreteL2DiagonalUnboundednessObstructionSurface.witness k)

/-- The obstruction witness unit probe belongs to the diagonal domain. -/
def concreteL2ObstructionUnitDomain (k : ℕ) : ConcreteL2DiagonalDomainCarrier :=
  concreteL2UnitDiagonalDomain
    (concreteL2DiagonalUnboundednessObstructionSurface.witness k)

/-- The diagonal action on the obstruction-selected unit vector exceeds the
requested threshold at the selected coordinate. -/
theorem concrete_l2_obstruction_unit_action_threshold_law (k : ℕ) :
    (k : ℝ) <
      concreteL2DiagonalRawAction (concreteL2ObstructionUnitDomain k)
        (concreteL2DiagonalUnboundednessObstructionSurface.witness k) := by
  rw [concreteL2ObstructionUnitDomain,
    concrete_l2_diagonal_raw_action_unit_self]
  exact concrete_l2_diagonal_obstruction_index_threshold_law k

/-- Bridge surface connecting the weight obstruction index to concrete unit
probes.  It only says that the threshold witness can be realized by an explicit
unit probe in the diagonal domain.  It is not an operator-norm unboundedness
theorem, not a closed-operator theorem, not graph closure, not density, and not
self-adjointness. -/
structure ConcreteL2UnitObstructionBridgeSurface where
  obstructionIndexReady : concreteAnalyticSpineL2ObstructionIndexSurfaceReady
  unitProbeReady : concreteAnalyticSpineL2UnitProbeSurfaceReady
  obstructionUnitProbe : ℕ → ConcreteL2RealSequence
  obstructionUnitDomain : ℕ → ConcreteL2DiagonalDomainCarrier
  actionThresholdLaw : ∀ k : ℕ,
    (k : ℝ) <
      concreteL2DiagonalRawAction (obstructionUnitDomain k)
        (concreteL2DiagonalUnboundednessObstructionSurface.witness k)
  boundaryNotOperatorNormUnboundednessTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotGraphClosureTheorem : Prop
  boundaryNotDensityTheorem : Prop
  boundaryNotSelfAdjointness : Prop

/-- The concrete bridge from obstruction witnesses to unit probes. -/
def concreteL2UnitObstructionBridgeSurface :
    ConcreteL2UnitObstructionBridgeSurface :=
  { obstructionIndexReady :=
      concrete_analytic_spine_l2_obstruction_index_surface_ready
    unitProbeReady := concrete_analytic_spine_l2_unit_probe_surface_ready
    obstructionUnitProbe := concreteL2ObstructionUnitProbe
    obstructionUnitDomain := concreteL2ObstructionUnitDomain
    actionThresholdLaw := concrete_l2_obstruction_unit_action_threshold_law
    boundaryNotOperatorNormUnboundednessTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotGraphClosureTheorem := True
    boundaryNotDensityTheorem := True
    boundaryNotSelfAdjointness := True }

/-- Readiness for the concrete `l2` unit-obstruction bridge surface. -/
def concreteAnalyticSpineL2UnitObstructionBridgeSurfaceReady : Prop :=
  concreteAnalyticSpineL2UnitProbeSurfaceReady ∧
  (∀ k : ℕ,
    (k : ℝ) <
      concreteL2DiagonalRawAction (concreteL2ObstructionUnitDomain k)
        (concreteL2DiagonalUnboundednessObstructionSurface.witness k)) ∧
  concreteL2UnitObstructionBridgeSurface.boundaryNotOperatorNormUnboundednessTheorem ∧
  concreteL2UnitObstructionBridgeSurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2UnitObstructionBridgeSurface.boundaryNotGraphClosureTheorem ∧
  concreteL2UnitObstructionBridgeSurface.boundaryNotDensityTheorem ∧
  concreteL2UnitObstructionBridgeSurface.boundaryNotSelfAdjointness

/-- Readiness theorem for the concrete `l2` unit-obstruction bridge surface. -/
theorem concrete_analytic_spine_l2_unit_obstruction_bridge_surface_ready :
    concreteAnalyticSpineL2UnitObstructionBridgeSurfaceReady := by
  unfold concreteAnalyticSpineL2UnitObstructionBridgeSurfaceReady
  exact And.intro concrete_analytic_spine_l2_unit_probe_surface_ready <|
    And.intro concrete_l2_obstruction_unit_action_threshold_law <|
      And.intro trivial <| And.intro trivial <| And.intro trivial <|
        And.intro trivial trivial

/-- Boundary marker for the concrete `l2` unit-obstruction bridge surface. -/
def concreteAnalyticSpineL2UnitObstructionBridgeHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2UnitObstructionBridgeSurfaceReady

/-- Boundary theorem for the concrete `l2` unit-obstruction bridge surface. -/
theorem concrete_analytic_spine_l2_unit_obstruction_bridge_hard_residual_boundary_held :
    concreteAnalyticSpineL2UnitObstructionBridgeHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_unit_obstruction_bridge_surface_ready

end

end MathlibAnalytic
end MGAP4D
