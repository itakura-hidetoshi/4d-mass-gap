import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonSystem

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Gauge action on physical positive links. -/
def CompactOrientedGaugeWilsonSystem.gaugeTransform
    (L : CompactOrientedGaugeWilsonSystem)
    (gamma : L.GaugeTransformation)
    (A : L.Configuration) : L.Configuration :=
  fun e => gamma (L.geometry.edgeSource e) * A e *
    (gamma (L.geometry.edgeTarget e))⁻¹

/-- Group value contributed by one signed boundary incidence. -/
def CompactOrientedGaugeWilsonSystem.stepValue
    (L : CompactOrientedGaugeWilsonSystem)
    (A : L.Configuration)
    (step : FiniteOrientedBoundaryStep L.geometry.Edge) : L.Gauge :=
  L.geometry.stepValue A step

/-- A signed incidence transforms using its actual oriented endpoints. -/
theorem compact_oriented_stepValue_gaugeTransform
    (L : CompactOrientedGaugeWilsonSystem)
    (gamma : L.GaugeTransformation)
    (A : L.Configuration)
    (step : FiniteOrientedBoundaryStep L.geometry.Edge) :
    L.stepValue (L.gaugeTransform gamma A) step =
      gamma (step.initial L.geometry.edgeSource L.geometry.edgeTarget) *
        L.stepValue A step *
        (gamma (step.terminal
          L.geometry.edgeSource L.geometry.edgeTarget))⁻¹ := by
  cases step with
  | mk edge orientation =>
      cases orientation <;>
        simp [CompactOrientedGaugeWilsonSystem.stepValue,
          CompactOrientedGaugeWilsonSystem.gaugeTransform,
          FiniteOrientedFourDimensionalPlaquetteGeometry.stepValue,
          FiniteOrientedBoundaryStep.initial,
          FiniteOrientedBoundaryStep.terminal] <;>
        group

/-- Ordered signed plaquette holonomy. -/
def CompactOrientedGaugeWilsonSystem.plaquetteHolonomy
    (L : CompactOrientedGaugeWilsonSystem)
    (A : L.Configuration)
    (p : L.geometry.Plaquette) : L.Gauge :=
  L.geometry.plaquetteHolonomy A p

/-- Signed plaquette holonomy transforms by conjugation at its initial vertex. -/
theorem compact_oriented_plaquetteHolonomy_gaugeTransform
    (L : CompactOrientedGaugeWilsonSystem)
    (gamma : L.GaugeTransformation)
    (A : L.Configuration)
    (p : L.geometry.Plaquette) :
    L.plaquetteHolonomy (L.gaugeTransform gamma A) p =
      gamma ((L.geometry.boundary p 0).initial
        L.geometry.edgeSource L.geometry.edgeTarget) *
        L.plaquetteHolonomy A p *
        (gamma ((L.geometry.boundary p 0).initial
          L.geometry.edgeSource L.geometry.edgeTarget))⁻¹ := by
  unfold CompactOrientedGaugeWilsonSystem.plaquetteHolonomy
    FiniteOrientedFourDimensionalPlaquetteGeometry.plaquetteHolonomy
  rw [compact_oriented_stepValue_gaugeTransform,
    compact_oriented_stepValue_gaugeTransform,
    compact_oriented_stepValue_gaugeTransform,
    compact_oriented_stepValue_gaugeTransform]
  rw [L.geometry.boundary_cycle_01 p,
    L.geometry.boundary_cycle_12 p,
    L.geometry.boundary_cycle_23 p,
    L.geometry.boundary_cycle_30 p]
  group

end

end MathlibAnalytic
end MGAP4D
