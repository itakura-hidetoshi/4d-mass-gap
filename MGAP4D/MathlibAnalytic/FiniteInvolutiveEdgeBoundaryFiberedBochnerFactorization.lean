import MGAP4D.MathlibAnalytic.FiniteInvolutiveEdgeBoundaryFiberedMeasureFactorization
import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonOSBochnerGram

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

namespace FiniteInvolutiveEdgeOrbitPartition

universe v w

variable {Edge : Type} [Fintype Edge]

/-- Boundary-fibered measure transport followed by the Bochner Gram identity. -/
theorem BoundaryFiberedMeasureFactorization.integral_pullback_inner_eq_boundary_norm_sq
    {P : FiniteInvolutiveEdgeOrbitPartition Edge} {Value : Type v}
    [MeasurableSpace Value]
    (M : BoundaryFiberedMeasureFactorization P Value)
    (FeatureHilbert : Type w) [NormedAddCommGroup FeatureHilbert]
    [InnerProductSpace ℝ FeatureHilbert] [CompleteSpace FeatureHilbert]
    (weightedFeature : P.BoundaryConfiguration Value →
      P.OpenHalfConfiguration Value → FeatureHilbert)
    (hWeightedFeatureIntegrable :
      ∀ b, Integrable (weightedFeature b) M.halfMeasure)
    (hKernelIntegrable : Integrable
      (fun z : P.BoundaryConfiguration Value ×
          (P.OpenHalfConfiguration Value × P.OpenHalfConfiguration Value) =>
        inner ℝ (weightedFeature z.1 z.2.1) (weightedFeature z.1 z.2.2))
      (M.boundaryMeasure.prod (M.halfMeasure.prod M.halfMeasure)))
    (hFiberKernelIntegrable : ∀ b, Integrable
      (fun z : P.OpenHalfConfiguration Value × P.OpenHalfConfiguration Value =>
        inner ℝ (weightedFeature b z.1) (weightedFeature b z.2))
      (M.halfMeasure.prod M.halfMeasure)) :
    (∫ U, inner ℝ
      (weightedFeature (P.boundaryFiberedCoordinates Value U).1
        (P.boundaryFiberedCoordinates Value U).2.1)
      (weightedFeature (P.boundaryFiberedCoordinates Value U).1
        (P.boundaryFiberedCoordinates Value U).2.2) ∂M.fullMeasure) =
      ∫ b, ‖∫ x, weightedFeature b x ∂M.halfMeasure‖ ^ 2
        ∂M.boundaryMeasure := by
  calc
    (∫ U,
        inner ℝ
          (weightedFeature
            (P.boundaryFiberedCoordinates Value U).1
            (P.boundaryFiberedCoordinates Value U).2.1)
          (weightedFeature
            (P.boundaryFiberedCoordinates Value U).1
            (P.boundaryFiberedCoordinates Value U).2.2)
        ∂M.fullMeasure) =
      ∫ b, ∫ x, ∫ y,
        inner ℝ (weightedFeature b x) (weightedFeature b y)
        ∂M.halfMeasure ∂M.halfMeasure ∂M.boundaryMeasure := by
          exact M.integral_pullback_eq_boundary_half_half
            (fun z =>
              inner ℝ
                (weightedFeature z.1 z.2.1)
                (weightedFeature z.1 z.2.2))
            hKernelIntegrable
            hFiberKernelIntegrable
    _ = ∫ b, ‖∫ x, weightedFeature b x ∂M.halfMeasure‖ ^ 2
          ∂M.boundaryMeasure := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun b => by
              simpa using
                iterated_integral_real_inner_eq_norm_integral_sq
                  M.halfMeasure
                  (weightedFeature b)
                  (hWeightedFeatureIntegrable b)

end FiniteInvolutiveEdgeOrbitPartition

end

end MathlibAnalytic
end MGAP4D
