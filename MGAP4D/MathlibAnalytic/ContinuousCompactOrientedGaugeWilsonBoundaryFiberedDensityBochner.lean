import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonBoundaryFiberedGibbsFactorization
import MGAP4D.MathlibAnalytic.FiniteInvolutiveEdgeBoundaryFiberedDensityBochnerFactorization

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

universe w

/-- Model-specific Hilbert factorization data for a continuous compact Wilson
Gibbs law in shared-boundary/open-half/open-half coordinates. -/
structure ContinuousCompactOrientedGaugeWilsonBoundaryFiberedDensityBochnerData
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (P : FiniteInvolutiveEdgeOrbitPartition C.base.geometry.Edge)
    (FeatureHilbert : Type w) [NormedAddCommGroup FeatureHilbert]
    [InnerProductSpace ℝ FeatureHilbert] [CompleteSpace FeatureHilbert] where
  fullObservable : C.base.Configuration → ℝ
  coordinateObservable :
    P.BoundaryConfiguration C.base.Gauge ×
      (P.OpenHalfConfiguration C.base.Gauge ×
        P.OpenHalfConfiguration C.base.Gauge) → ℝ
  fullObservable_eq_coordinateObservable :
    ∀ U, fullObservable U =
      coordinateObservable (P.boundaryFiberedCoordinates C.base.Gauge U)
  coordinateObservable_integrable :
    Integrable coordinateObservable
      (((P.boundaryPiMeasure (normalizedCompactHaar C.base.Gauge)).prod
        ((P.openHalfPiMeasure (normalizedCompactHaar C.base.Gauge)).prod
          (P.openHalfPiMeasure
            (normalizedCompactHaar C.base.Gauge)))).withDensity
        (C.boundaryFiberedGibbsDensity P))
  weightedFeature :
    P.BoundaryConfiguration C.base.Gauge →
      P.OpenHalfConfiguration C.base.Gauge → FeatureHilbert
  weightedFeature_integrable :
    ∀ b, Integrable (weightedFeature b)
      (P.openHalfPiMeasure (normalizedCompactHaar C.base.Gauge))
  density_toReal_mul_coordinateObservable_eq_inner :
    ∀ z, (C.boundaryFiberedGibbsDensity P z).toReal *
      coordinateObservable z =
        inner ℝ (weightedFeature z.1 z.2.1) (weightedFeature z.1 z.2.2)
  kernel_integrable :
    Integrable
      (fun z => inner ℝ
        (weightedFeature z.1 z.2.1) (weightedFeature z.1 z.2.2))
      ((P.boundaryPiMeasure (normalizedCompactHaar C.base.Gauge)).prod
        ((P.openHalfPiMeasure (normalizedCompactHaar C.base.Gauge)).prod
          (P.openHalfPiMeasure (normalizedCompactHaar C.base.Gauge))))
  fiberKernel_integrable :
    ∀ b, Integrable
      (fun z => inner ℝ (weightedFeature b z.1) (weightedFeature b z.2))
      ((P.openHalfPiMeasure (normalizedCompactHaar C.base.Gauge)).prod
        (P.openHalfPiMeasure (normalizedCompactHaar C.base.Gauge)))

/-- Convert concrete compact Wilson Gibbs data into the generic
boundary-fibered density-weighted Bochner factorization. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonBoundaryFiberedDensityBochnerData.toDensityBochnerFactorization
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    {P : FiniteInvolutiveEdgeOrbitPartition C.base.geometry.Edge}
    {FeatureHilbert : Type w} [NormedAddCommGroup FeatureHilbert]
    [InnerProductSpace ℝ FeatureHilbert] [CompleteSpace FeatureHilbert]
    (B : ContinuousCompactOrientedGaugeWilsonBoundaryFiberedDensityBochnerData
      C P FeatureHilbert) :
    P.BoundaryFiberedDensityBochnerFactorization C.base.Gauge FeatureHilbert where
  fullMeasure := C.gibbsMeasure
  boundaryMeasure := P.boundaryPiMeasure (normalizedCompactHaar C.base.Gauge)
  halfMeasure := P.openHalfPiMeasure (normalizedCompactHaar C.base.Gauge)
  boundaryMeasure_sfinite := inferInstance
  halfMeasure_sfinite := inferInstance
  coordinates_aemeasurable :=
    (P.boundaryFiberedCoordinates_measurable C.base.Gauge).aemeasurable
  density := C.boundaryFiberedGibbsDensity P
  density_aemeasurable :=
    (C.boundaryFiberedGibbsDensity_measurable P).aemeasurable
  density_lt_top_ae := Filter.Eventually.of_forall fun z => by
    simp [ContinuousCompactOrientedGaugeWilsonSystem.boundaryFiberedGibbsDensity]
  map_coordinates_fullMeasure :=
    C.map_boundaryFiberedCoordinates_gibbsMeasure P
  fullObservable := B.fullObservable
  coordinateObservable := B.coordinateObservable
  fullObservable_eq_coordinateObservable :=
    B.fullObservable_eq_coordinateObservable
  coordinateObservable_integrable := B.coordinateObservable_integrable
  weightedFeature := B.weightedFeature
  weightedFeature_integrable := B.weightedFeature_integrable
  density_toReal_mul_coordinateObservable_eq_inner :=
    B.density_toReal_mul_coordinateObservable_eq_inner
  kernel_integrable := B.kernel_integrable
  fiberKernel_integrable := B.fiberKernel_integrable

/-- The actual finite-volume compact Wilson Gibbs expectation is a boundary
integral of squared conditional Hilbert moments whenever the density-weighted
reflected observable has the supplied Gram factorization. -/
theorem continuous_compact_oriented_boundaryFiberedDensityBochner_integral_eq_norm_sq
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    {P : FiniteInvolutiveEdgeOrbitPartition C.base.geometry.Edge}
    {FeatureHilbert : Type w} [NormedAddCommGroup FeatureHilbert]
    [InnerProductSpace ℝ FeatureHilbert] [CompleteSpace FeatureHilbert]
    (B : ContinuousCompactOrientedGaugeWilsonBoundaryFiberedDensityBochnerData
      C P FeatureHilbert) :
    (∫ U, B.fullObservable U ∂C.gibbsMeasure) =
      ∫ b, ‖∫ x, B.weightedFeature b x
        ∂P.openHalfPiMeasure (normalizedCompactHaar C.base.Gauge)‖ ^ 2
        ∂P.boundaryPiMeasure (normalizedCompactHaar C.base.Gauge) := by
  exact B.toDensityBochnerFactorization.integral_eq_boundary_norm_sq

end

end MathlibAnalytic
end MGAP4D
