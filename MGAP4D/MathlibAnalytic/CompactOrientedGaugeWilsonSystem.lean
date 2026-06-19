import MGAP4D.MathlibAnalytic.CompactGaugeWilsonHaarGibbsMeasure
import MGAP4D.MathlibAnalytic.FiniteOrientedFourDimensionalPlaquetteGeometry

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A compact-gauge Wilson system on physical positive links with signed
plaquette-boundary incidences. -/
structure CompactOrientedGaugeWilsonSystem where
  Gauge : Type
  [gaugeGroup : Group Gauge]
  [gaugeTopology : TopologicalSpace Gauge]
  [gaugeTopologicalGroup : IsTopologicalGroup Gauge]
  [gaugeCompact : CompactSpace Gauge]
  [gaugeSecondCountable : SecondCountableTopology Gauge]
  [gaugeMeasurableSpace : MeasurableSpace Gauge]
  [gaugeBorel : BorelSpace Gauge]
  [gaugeNontrivial : Nontrivial Gauge]
  geometry : FiniteOrientedFourDimensionalPlaquetteGeometry
  plaquetteEnergy : Gauge → ℝ
  plaquetteEnergy_nonneg : ∀ g, 0 ≤ plaquetteEnergy g
  plaquetteEnergy_conjInvariant :
    ∀ h g, plaquetteEnergy (h * g * h⁻¹) = plaquetteEnergy g
  beta : ℝ
  beta_nonneg : 0 ≤ beta

attribute [instance]
  CompactOrientedGaugeWilsonSystem.gaugeGroup
  CompactOrientedGaugeWilsonSystem.gaugeTopology
  CompactOrientedGaugeWilsonSystem.gaugeTopologicalGroup
  CompactOrientedGaugeWilsonSystem.gaugeCompact
  CompactOrientedGaugeWilsonSystem.gaugeSecondCountable
  CompactOrientedGaugeWilsonSystem.gaugeMeasurableSpace
  CompactOrientedGaugeWilsonSystem.gaugeBorel
  CompactOrientedGaugeWilsonSystem.gaugeNontrivial

abbrev CompactOrientedGaugeWilsonSystem.Configuration
    (L : CompactOrientedGaugeWilsonSystem) : Type :=
  L.geometry.Edge → L.Gauge

abbrev CompactOrientedGaugeWilsonSystem.GaugeTransformation
    (L : CompactOrientedGaugeWilsonSystem) : Type :=
  L.geometry.Vertex → L.Gauge

end

end MathlibAnalytic
end MGAP4D
