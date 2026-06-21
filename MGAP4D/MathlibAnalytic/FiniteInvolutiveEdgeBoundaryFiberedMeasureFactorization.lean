import MGAP4D.MathlibAnalytic.FiniteInvolutiveEdgeBoundaryFiberedCoordinates
import Mathlib.MeasureTheory.Integral.Prod

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

namespace FiniteInvolutiveEdgeOrbitPartition

universe v

variable {Edge : Type} [Fintype Edge]

/-- Measure-theoretic realization of the exact boundary-fibered coordinate
system attached to a finite involutive edge partition.

The datum does not assume that an interacting Gibbs law is itself an
unconditional product.  It records only an exact pushforward identity under
the coordinate equivalence.  In applications, the right-hand side may be a
reference product measure, while the Gibbs interaction is retained in the
transformed observable or in an additional density. -/
structure BoundaryFiberedMeasureFactorization
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    (Value : Type v)
    [MeasurableSpace Value] where
  fullMeasure : Measure (Edge → Value)
  boundaryMeasure : Measure (P.BoundaryConfiguration Value)
  halfMeasure : Measure (P.OpenHalfConfiguration Value)
  coordinates_aemeasurable :
    AEMeasurable (P.boundaryFiberedCoordinates Value) fullMeasure
  map_coordinates_fullMeasure :
    Measure.map (P.boundaryFiberedCoordinates Value) fullMeasure =
      boundaryMeasure.prod (halfMeasure.prod halfMeasure)

/-- Transport a full-configuration integral through the exact
boundary-fibered coordinates and then apply Fubini twice.

The second integrability hypothesis is deliberately fiberwise.  It avoids
claiming a pointwise conditional Fubini statement from a merely almost-everywhere
section theorem. -/
theorem BoundaryFiberedMeasureFactorization.integral_eq_boundary_half_half
    {P : FiniteInvolutiveEdgeOrbitPartition Edge}
    {Value : Type v}
    [MeasurableSpace Value]
    (M : BoundaryFiberedMeasureFactorization P Value)
    (fullObservable : (Edge → Value) → ℝ)
    (coordinateObservable :
      P.BoundaryConfiguration Value ×
        (P.OpenHalfConfiguration Value × P.OpenHalfConfiguration Value) → ℝ)
    (hObservable :
      ∀ U,
        fullObservable U =
          coordinateObservable (P.boundaryFiberedCoordinates Value U))
    (hCoordinateIntegrable :
      Integrable coordinateObservable
        (M.boundaryMeasure.prod (M.halfMeasure.prod M.halfMeasure)))
    (hFiberIntegrable :
      ∀ b,
        Integrable (fun z => coordinateObservable (b, z))
          (M.halfMeasure.prod M.halfMeasure)) :
    (∫ U, fullObservable U ∂M.fullMeasure) =
      ∫ b, ∫ x, ∫ y, coordinateObservable (b, (x, y))
        ∂M.halfMeasure ∂M.halfMeasure ∂M.boundaryMeasure := by
  have hCoordinateMapMeasurable :
      AEStronglyMeasurable coordinateObservable
        (Measure.map (P.boundaryFiberedCoordinates Value) M.fullMeasure) := by
    rw [M.map_coordinates_fullMeasure]
    exact hCoordinateIntegrable.aestronglyMeasurable
  calc
    (∫ U, fullObservable U ∂M.fullMeasure) =
        ∫ U,
          coordinateObservable (P.boundaryFiberedCoordinates Value U)
          ∂M.fullMeasure := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hObservable
    _ = ∫ z, coordinateObservable z
          ∂Measure.map (P.boundaryFiberedCoordinates Value) M.fullMeasure := by
            symm
            exact MeasureTheory.integral_map
              M.coordinates_aemeasurable hCoordinateMapMeasurable
    _ = ∫ z, coordinateObservable z
          ∂M.boundaryMeasure.prod (M.halfMeasure.prod M.halfMeasure) := by
            rw [M.map_coordinates_fullMeasure]
    _ = ∫ b, ∫ z, coordinateObservable (b, z)
          ∂M.halfMeasure.prod M.halfMeasure ∂M.boundaryMeasure := by
            exact MeasureTheory.integral_prod _ hCoordinateIntegrable
    _ = ∫ b, ∫ x, ∫ y, coordinateObservable (b, (x, y))
          ∂M.halfMeasure ∂M.halfMeasure ∂M.boundaryMeasure := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun b =>
              MeasureTheory.integral_prod _ (hFiberIntegrable b)

/-- Direct form of the transport theorem when the full observable is defined
as the pullback of a boundary-fibered observable. -/
theorem BoundaryFiberedMeasureFactorization.integral_pullback_eq_boundary_half_half
    {P : FiniteInvolutiveEdgeOrbitPartition Edge}
    {Value : Type v}
    [MeasurableSpace Value]
    (M : BoundaryFiberedMeasureFactorization P Value)
    (coordinateObservable :
      P.BoundaryConfiguration Value ×
        (P.OpenHalfConfiguration Value × P.OpenHalfConfiguration Value) → ℝ)
    (hCoordinateIntegrable :
      Integrable coordinateObservable
        (M.boundaryMeasure.prod (M.halfMeasure.prod M.halfMeasure)))
    (hFiberIntegrable :
      ∀ b,
        Integrable (fun z => coordinateObservable (b, z))
          (M.halfMeasure.prod M.halfMeasure)) :
    (∫ U,
        coordinateObservable (P.boundaryFiberedCoordinates Value U)
        ∂M.fullMeasure) =
      ∫ b, ∫ x, ∫ y, coordinateObservable (b, (x, y))
        ∂M.halfMeasure ∂M.halfMeasure ∂M.boundaryMeasure := by
  exact M.integral_eq_boundary_half_half
    (fun U => coordinateObservable (P.boundaryFiberedCoordinates Value U))
    coordinateObservable
    (fun _ => rfl)
    hCoordinateIntegrable
    hFiberIntegrable

end FiniteInvolutiveEdgeOrbitPartition

end

end MathlibAnalytic
end MGAP4D
