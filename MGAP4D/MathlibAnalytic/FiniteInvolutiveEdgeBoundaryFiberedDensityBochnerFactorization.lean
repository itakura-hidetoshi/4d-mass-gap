import MGAP4D.MathlibAnalytic.FiniteInvolutiveEdgeBoundaryFiberedCoordinates
import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonOSBochnerGram
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace FiniteInvolutiveEdgeOrbitPartition

universe v w

variable {Edge : Type} [Fintype Edge]

/-- Density-weighted boundary-fibered Gram data.

The full interacting law is transported to a density over one shared boundary
configuration and two copies of the selected open half.  The product of the
transported density with the reflected observable is then identified pointwise
with a Hilbert inner product. -/
structure BoundaryFiberedDensityBochnerFactorization
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    (Value : Type v) [MeasurableSpace Value]
    (FeatureHilbert : Type w) [NormedAddCommGroup FeatureHilbert]
    [InnerProductSpace ℝ FeatureHilbert] [CompleteSpace FeatureHilbert] where
  fullMeasure : Measure (Edge → Value)
  boundaryMeasure : Measure (P.BoundaryConfiguration Value)
  halfMeasure : Measure (P.OpenHalfConfiguration Value)
  boundaryMeasure_sfinite : SFinite boundaryMeasure
  halfMeasure_sfinite : SFinite halfMeasure
  coordinates_aemeasurable :
    AEMeasurable (P.boundaryFiberedCoordinates Value) fullMeasure
  density :
    P.BoundaryConfiguration Value ×
      (P.OpenHalfConfiguration Value × P.OpenHalfConfiguration Value) → ℝ≥0∞
  density_aemeasurable :
    AEMeasurable density (boundaryMeasure.prod (halfMeasure.prod halfMeasure))
  density_lt_top_ae :
    ∀ᵐ z ∂(boundaryMeasure.prod (halfMeasure.prod halfMeasure)), density z < ∞
  map_coordinates_fullMeasure :
    Measure.map (P.boundaryFiberedCoordinates Value) fullMeasure =
      (boundaryMeasure.prod (halfMeasure.prod halfMeasure)).withDensity density
  fullObservable : (Edge → Value) → ℝ
  coordinateObservable :
    P.BoundaryConfiguration Value ×
      (P.OpenHalfConfiguration Value × P.OpenHalfConfiguration Value) → ℝ
  fullObservable_eq_coordinateObservable :
    ∀ U, fullObservable U =
      coordinateObservable (P.boundaryFiberedCoordinates Value U)
  coordinateObservable_integrable :
    Integrable coordinateObservable
      ((boundaryMeasure.prod (halfMeasure.prod halfMeasure)).withDensity density)
  weightedFeature :
    P.BoundaryConfiguration Value →
      P.OpenHalfConfiguration Value → FeatureHilbert
  weightedFeature_integrable :
    ∀ b, Integrable (weightedFeature b) halfMeasure
  density_toReal_mul_coordinateObservable_eq_inner :
    ∀ z, (density z).toReal * coordinateObservable z =
      inner ℝ (weightedFeature z.1 z.2.1) (weightedFeature z.1 z.2.2)
  kernel_integrable :
    Integrable
      (fun z => inner ℝ
        (weightedFeature z.1 z.2.1) (weightedFeature z.1 z.2.2))
      (boundaryMeasure.prod (halfMeasure.prod halfMeasure))
  fiberKernel_integrable :
    ∀ b, Integrable
      (fun z => inner ℝ (weightedFeature b z.1) (weightedFeature b z.2))
      (halfMeasure.prod halfMeasure)

attribute [instance]
  BoundaryFiberedDensityBochnerFactorization.boundaryMeasure_sfinite
  BoundaryFiberedDensityBochnerFactorization.halfMeasure_sfinite

/-- Density transport, two applications of Fubini, and the fiberwise Bochner
Gram identity reduce the interacting full-configuration integral to a boundary
integral of squared Hilbert moments. -/
theorem BoundaryFiberedDensityBochnerFactorization.integral_eq_boundary_norm_sq
    {P : FiniteInvolutiveEdgeOrbitPartition Edge}
    {Value : Type v} [MeasurableSpace Value]
    {FeatureHilbert : Type w} [NormedAddCommGroup FeatureHilbert]
    [InnerProductSpace ℝ FeatureHilbert] [CompleteSpace FeatureHilbert]
    (C : BoundaryFiberedDensityBochnerFactorization P Value FeatureHilbert) :
    (∫ U, C.fullObservable U ∂C.fullMeasure) =
      ∫ b, ‖∫ x, C.weightedFeature b x ∂C.halfMeasure‖ ^ 2
        ∂C.boundaryMeasure := by
  let referenceMeasure : Measure
      (P.BoundaryConfiguration Value ×
        (P.OpenHalfConfiguration Value × P.OpenHalfConfiguration Value)) :=
    C.boundaryMeasure.prod (C.halfMeasure.prod C.halfMeasure)
  have hCoordinateMapMeasurable :
      AEStronglyMeasurable C.coordinateObservable
        (Measure.map (P.boundaryFiberedCoordinates Value) C.fullMeasure) := by
    rw [C.map_coordinates_fullMeasure]
    exact C.coordinateObservable_integrable.aestronglyMeasurable
  calc
    (∫ U, C.fullObservable U ∂C.fullMeasure) =
        ∫ U, C.coordinateObservable (P.boundaryFiberedCoordinates Value U)
          ∂C.fullMeasure := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall
              C.fullObservable_eq_coordinateObservable
    _ = ∫ z, C.coordinateObservable z
          ∂Measure.map (P.boundaryFiberedCoordinates Value) C.fullMeasure := by
            symm
            exact MeasureTheory.integral_map
              C.coordinates_aemeasurable hCoordinateMapMeasurable
    _ = ∫ z, C.coordinateObservable z
          ∂referenceMeasure.withDensity C.density := by
            rw [C.map_coordinates_fullMeasure]
    _ = ∫ z, (C.density z).toReal • C.coordinateObservable z
          ∂referenceMeasure := by
            exact integral_withDensity_eq_integral_toReal_smul₀
              C.density_aemeasurable C.density_lt_top_ae C.coordinateObservable
    _ = ∫ z, inner ℝ
          (C.weightedFeature z.1 z.2.1)
          (C.weightedFeature z.1 z.2.2) ∂referenceMeasure := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun z => by
              simpa [smul_eq_mul] using
                C.density_toReal_mul_coordinateObservable_eq_inner z
    _ = ∫ b, ∫ z, inner ℝ
          (C.weightedFeature b z.1) (C.weightedFeature b z.2)
          ∂C.halfMeasure.prod C.halfMeasure ∂C.boundaryMeasure := by
            exact MeasureTheory.integral_prod _ C.kernel_integrable
    _ = ∫ b, ∫ x, ∫ y, inner ℝ
          (C.weightedFeature b x) (C.weightedFeature b y)
          ∂C.halfMeasure ∂C.halfMeasure ∂C.boundaryMeasure := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun b =>
              MeasureTheory.integral_prod _ (C.fiberKernel_integrable b)
    _ = ∫ b, ‖∫ x, C.weightedFeature b x ∂C.halfMeasure‖ ^ 2
          ∂C.boundaryMeasure := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun b => by
              simpa using iterated_integral_real_inner_eq_norm_integral_sq
                C.halfMeasure (C.weightedFeature b)
                (C.weightedFeature_integrable b)

end FiniteInvolutiveEdgeOrbitPartition

end

end MathlibAnalytic
end MGAP4D
