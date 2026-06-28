import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonBoundaryFiberedGibbsDensity

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Exact pushforward of the Wilson Gibbs law to boundary-fibered coordinates. -/
theorem ContinuousCompactOrientedGaugeWilsonSystem.map_boundaryFiberedCoordinates_gibbsMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (P : FiniteInvolutiveEdgeOrbitPartition C.base.geometry.Edge) :
    Measure.map (P.boundaryFiberedCoordinates C.base.Gauge) C.gibbsMeasure =
      ((P.boundaryPiMeasure (normalizedCompactHaar C.base.Gauge)).prod
        ((P.openHalfPiMeasure (normalizedCompactHaar C.base.Gauge)).prod
          (P.openHalfPiMeasure
            (normalizedCompactHaar C.base.Gauge)))).withDensity
        (C.boundaryFiberedGibbsDensity P) := by
  have hfun :
      ((P.boundaryFiberedPiMeasurableEquiv C.base.Gauge :
        C.base.Configuration ≃ᵐ
          P.BoundaryConfiguration C.base.Gauge ×
            (P.OpenHalfConfiguration C.base.Gauge ×
              P.OpenHalfConfiguration C.base.Gauge)) :
        C.base.Configuration →
          P.BoundaryConfiguration C.base.Gauge ×
            (P.OpenHalfConfiguration C.base.Gauge ×
              P.OpenHalfConfiguration C.base.Gauge)) =
        P.boundaryFiberedCoordinates C.base.Gauge := by
    funext A
    exact P.boundaryFiberedPiMeasurableEquiv_apply C.base.Gauge A
  rw [← hfun]
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsMeasure
  rw [compact_oriented_gibbsMeasure_eq_withDensity]
  rw [MeasurableEquiv.map_withDensity_comp_symm_transport]
  · unfold CompactOrientedGaugeWilsonSystem.configurationHaarMeasure
    rw [(P.boundaryFiberedPiMeasurableEquiv_measurePreserving
      (normalizedCompactHaar C.base.Gauge)).map_eq]
    rfl
  · exact ENNReal.measurable_ofReal.comp
      ((continuous_compact_oriented_boltzmannFactor C).measurable.div
        measurable_const)

end

end MathlibAnalytic
end MGAP4D
