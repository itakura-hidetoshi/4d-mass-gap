import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonBoundaryFiberedGibbsTransport

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Wilson Gibbs density in shared-boundary/open-half/open-half coordinates. -/
noncomputable def ContinuousCompactOrientedGaugeWilsonSystem.boundaryFiberedGibbsDensity
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (P : FiniteInvolutiveEdgeOrbitPartition C.base.geometry.Edge) :
    P.BoundaryConfiguration C.base.Gauge ×
        (P.OpenHalfConfiguration C.base.Gauge ×
          P.OpenHalfConfiguration C.base.Gauge) → ℝ≥0∞ :=
  fun z => ENNReal.ofReal
    (Real.exp
        (C.base.gibbsExponent
          ((P.boundaryFiberedPiMeasurableEquiv C.base.Gauge).symm z)) /
      C.base.partitionFunction)

/-- The boundary-fibered Wilson Gibbs density is measurable. -/
theorem ContinuousCompactOrientedGaugeWilsonSystem.boundaryFiberedGibbsDensity_measurable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (P : FiniteInvolutiveEdgeOrbitPartition C.base.geometry.Edge) :
    Measurable (C.boundaryFiberedGibbsDensity P) := by
  have hWeight : Measurable (fun A : C.base.Configuration =>
      Real.exp (C.base.gibbsExponent A) / C.base.partitionFunction) :=
    (continuous_compact_oriented_boltzmannFactor C).measurable.div measurable_const
  unfold ContinuousCompactOrientedGaugeWilsonSystem.boundaryFiberedGibbsDensity
  exact ENNReal.measurable_ofReal.comp
    (hWeight.comp
      (P.boundaryFiberedPiMeasurableEquiv C.base.Gauge).symm.measurable)

end

end MathlibAnalytic
end MGAP4D
