import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonHaarGibbsMeasure
import MGAP4D.MathlibAnalytic.FiniteInvolutiveEdgeBoundaryFiberedPiMeasure

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The product normalized Haar law of any finite compact oriented Wilson system
has the canonical shared-boundary/open-half/open-half factorization associated
to every reflection-compatible partition of its physical positive links. -/
noncomputable def
    CompactOrientedGaugeWilsonSystem.boundaryFiberedHaarMeasureFactorization
    (L : CompactOrientedGaugeWilsonSystem)
    (P : FiniteInvolutiveEdgeOrbitPartition L.geometry.Edge) :
    P.BoundaryFiberedMeasureFactorization L.Gauge :=
  P.boundaryFiberedPiMeasureFactorization (normalizedCompactHaar L.Gauge)

@[simp]
theorem CompactOrientedGaugeWilsonSystem.boundaryFiberedHaarMeasureFactorization_fullMeasure
    (L : CompactOrientedGaugeWilsonSystem)
    (P : FiniteInvolutiveEdgeOrbitPartition L.geometry.Edge) :
    (L.boundaryFiberedHaarMeasureFactorization P).fullMeasure =
      L.configurationHaarMeasure :=
  rfl

@[simp]
theorem CompactOrientedGaugeWilsonSystem.boundaryFiberedHaarMeasureFactorization_boundaryMeasure
    (L : CompactOrientedGaugeWilsonSystem)
    (P : FiniteInvolutiveEdgeOrbitPartition L.geometry.Edge) :
    (L.boundaryFiberedHaarMeasureFactorization P).boundaryMeasure =
      P.boundaryPiMeasure (normalizedCompactHaar L.Gauge) :=
  rfl

@[simp]
theorem CompactOrientedGaugeWilsonSystem.boundaryFiberedHaarMeasureFactorization_halfMeasure
    (L : CompactOrientedGaugeWilsonSystem)
    (P : FiniteInvolutiveEdgeOrbitPartition L.geometry.Edge) :
    (L.boundaryFiberedHaarMeasureFactorization P).halfMeasure =
      P.openHalfPiMeasure (normalizedCompactHaar L.Gauge) :=
  rfl

/-- Exact pushforward identity for the physical configuration Haar law under the
geometric boundary-fibered coordinate map. -/
theorem CompactOrientedGaugeWilsonSystem.map_boundaryFiberedCoordinates_configurationHaarMeasure
    (L : CompactOrientedGaugeWilsonSystem)
    (P : FiniteInvolutiveEdgeOrbitPartition L.geometry.Edge) :
    Measure.map (P.boundaryFiberedCoordinates L.Gauge)
        L.configurationHaarMeasure =
      (P.boundaryPiMeasure (normalizedCompactHaar L.Gauge)).prod
        ((P.openHalfPiMeasure (normalizedCompactHaar L.Gauge)).prod
          (P.openHalfPiMeasure (normalizedCompactHaar L.Gauge))) := by
  simpa using P.map_boundaryFiberedCoordinates_pi
    (normalizedCompactHaar L.Gauge)

end

end MathlibAnalytic
end MGAP4D
