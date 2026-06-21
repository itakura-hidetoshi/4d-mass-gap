import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonBoundaryFiberedHaarFactorization
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonSystem
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- A measurable equivalence transports a density by composition with its
inverse.  This is the exact change-of-coordinates identity needed for the
boundary-fibered Wilson Gibbs law. -/
theorem map_withDensity_measurableEquiv
    {α β : Type*}
    [MeasurableSpace α]
    [MeasurableSpace β]
    (e : α ≃ᵐ β)
    (μ : Measure α)
    (f : α → ℝ≥0∞)
    (hf : Measurable f) :
    Measure.map e (μ.withDensity f) =
      (Measure.map e μ).withDensity (fun y => f (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs]
  rw [withDensity_apply _ (hs.preimage e.measurable)]
  rw [withDensity_apply _ hs]
  rw [setLIntegral_map hs (hf.comp e.symm.measurable) e.measurable]
  simp

/-- Wilson Gibbs density written in canonical shared-boundary/open-half
coordinates.  The inverse measurable equivalence reconstructs the unique full
physical-link configuration, so reflection-fixed links occur only once. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.boundaryFiberedGibbsDensity
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
theorem
    ContinuousCompactOrientedGaugeWilsonSystem.boundaryFiberedGibbsDensity_measurable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (P : FiniteInvolutiveEdgeOrbitPartition C.base.geometry.Edge) :
    Measurable (C.boundaryFiberedGibbsDensity P) := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.boundaryFiberedGibbsDensity
  fun_prop

/-- Exact pushforward of a continuous compact oriented Wilson Gibbs law through
shared-boundary/open-half/open-half coordinates.

The reference measure is the already constructed boundary-fibered product Haar
law.  All interaction, including the crossing plaquettes, remains in the
explicit pulled-back Gibbs density. -/
theorem
    ContinuousCompactOrientedGaugeWilsonSystem.map_boundaryFiberedCoordinates_gibbsMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (P : FiniteInvolutiveEdgeOrbitPartition C.base.geometry.Edge) :
    Measure.map (P.boundaryFiberedCoordinates C.base.Gauge) C.gibbsMeasure =
      ((P.boundaryPiMeasure (normalizedCompactHaar C.base.Gauge)).prod
        ((P.openHalfPiMeasure (normalizedCompactHaar C.base.Gauge)).prod
          (P.openHalfPiMeasure
            (normalizedCompactHaar C.base.Gauge)))).withDensity
        (C.boundaryFiberedGibbsDensity P) := by
  let e := P.boundaryFiberedPiMeasurableEquiv C.base.Gauge
  have hfun :
      (e : C.base.Configuration →
        P.BoundaryConfiguration C.base.Gauge ×
          (P.OpenHalfConfiguration C.base.Gauge ×
            P.OpenHalfConfiguration C.base.Gauge)) =
        P.boundaryFiberedCoordinates C.base.Gauge := by
    funext A
    exact P.boundaryFiberedPiMeasurableEquiv_apply C.base.Gauge A
  rw [← hfun]
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsMeasure
  rw [compact_oriented_gibbsMeasure_eq_withDensity]
  rw [map_withDensity_measurableEquiv]
  · rw [(P.boundaryFiberedPiMeasurableEquiv_measurePreserving
      (normalizedCompactHaar C.base.Gauge)).map_eq]
    rfl
  · fun_prop

end

end MathlibAnalytic
end MGAP4D
