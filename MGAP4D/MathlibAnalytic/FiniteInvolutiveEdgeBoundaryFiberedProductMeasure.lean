import MGAP4D.MathlibAnalytic.FiniteInvolutiveEdgeBoundaryFiberedIndexEquiv
import MGAP4D.MathlibAnalytic.FiniteInvolutiveEdgeBoundaryFiberedMeasureFactorization
import Mathlib.MeasureTheory.Constructions.Pi

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

namespace FiniteInvolutiveEdgeOrbitPartition

universe v

variable {Edge : Type} [Fintype Edge]

/-- Measurable realization of the exact boundary-fibered coordinate equivalence.

It is assembled from three canonical measurable equivalences:

1. reindex the full edge function by the reflection-orbit index equivalence;
2. split fixed edges from the two open-half copies;
3. split the two open-half copies from one another. -/
def boundaryFiberedMeasurableEquiv
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    (Value : Type v)
    [MeasurableSpace Value] :
    (Edge → Value) ≃ᵐ
      P.BoundaryConfiguration Value ×
        (P.OpenHalfConfiguration Value × P.OpenHalfConfiguration Value) :=
  (MeasurableEquiv.piCongrLeft
      (fun _ : P.BoundaryFiberedIndex => Value)
      P.boundaryFiberedIndexEquiv).trans
    ((MeasurableEquiv.sumPiEquivProdPi
        (fun _ : P.FixedEdge ⊕ (P.PositiveEdge ⊕ P.PositiveEdge) => Value)).trans
      ((MeasurableEquiv.refl (P.BoundaryConfiguration Value)).prodCongr
        (MeasurableEquiv.sumPiEquivProdPi
          (fun _ : P.PositiveEdge ⊕ P.PositiveEdge => Value))))

/-- The canonical measurable equivalence has exactly the same underlying
function as the previously constructed explicit boundary-fibered coordinates. -/
theorem boundaryFiberedMeasurableEquiv_coe
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    (Value : Type v)
    [MeasurableSpace Value] :
    ((P.boundaryFiberedMeasurableEquiv Value :
        (Edge → Value) ≃ᵐ
          P.BoundaryConfiguration Value ×
            (P.OpenHalfConfiguration Value × P.OpenHalfConfiguration Value)) :
      (Edge → Value) →
        P.BoundaryConfiguration Value ×
          (P.OpenHalfConfiguration Value × P.OpenHalfConfiguration Value)) =
      (P.boundaryFiberedCoordinates Value :
        (Edge → Value) →
          P.BoundaryConfiguration Value ×
            (P.OpenHalfConfiguration Value × P.OpenHalfConfiguration Value)) := by
  funext A
  apply Prod.ext
  · funext e
    change
      (MeasurableEquiv.piCongrLeft
        (fun _ : P.BoundaryFiberedIndex => Value)
        P.boundaryFiberedIndexEquiv A) (Sum.inl e) = A e.1
    rw [← P.boundaryFiberedIndexEquiv_apply_fixed e]
    exact MeasurableEquiv.piCongrLeft_apply_apply
      P.boundaryFiberedIndexEquiv A e.1
  · apply Prod.ext
    · funext e
      change
        (MeasurableEquiv.piCongrLeft
          (fun _ : P.BoundaryFiberedIndex => Value)
          P.boundaryFiberedIndexEquiv A) (Sum.inr (Sum.inl e)) = A e.1
      rw [← P.boundaryFiberedIndexEquiv_apply_positive e]
      exact MeasurableEquiv.piCongrLeft_apply_apply
        P.boundaryFiberedIndexEquiv A e.1
    · funext e
      change
        (MeasurableEquiv.piCongrLeft
          (fun _ : P.BoundaryFiberedIndex => Value)
          P.boundaryFiberedIndexEquiv A) (Sum.inr (Sum.inr e)) =
            A (P.reflection e.1)
      rw [← P.boundaryFiberedIndexEquiv_apply_reflected_positive e]
      exact MeasurableEquiv.piCongrLeft_apply_apply
        P.boundaryFiberedIndexEquiv A (P.reflection e.1)

@[simp]
theorem boundaryFiberedMeasurableEquiv_apply
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    (Value : Type v)
    [MeasurableSpace Value]
    (A : Edge → Value) :
    P.boundaryFiberedMeasurableEquiv Value A =
      P.boundaryFiberedCoordinates Value A := by
  exact congr_fun (P.boundaryFiberedMeasurableEquiv_coe Value) A

/-- A finite product of one common sigma-finite measure is preserved by the
exact boundary-fibered coordinate equivalence. -/
theorem measurePreserving_boundaryFiberedMeasurableEquiv
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    (Value : Type v)
    [MeasurableSpace Value]
    (mu : Measure Value)
    [SigmaFinite mu] :
    MeasurePreserving
      (P.boundaryFiberedMeasurableEquiv Value)
      (Measure.pi fun _ : Edge => mu)
      ((Measure.pi fun _ : P.FixedEdge => mu).prod
        ((Measure.pi fun _ : P.PositiveEdge => mu).prod
          (Measure.pi fun _ : P.PositiveEdge => mu))) := by
  let reindex :
      (Edge → Value) ≃ᵐ (P.BoundaryFiberedIndex → Value) :=
    MeasurableEquiv.piCongrLeft
      (fun _ : P.BoundaryFiberedIndex => Value)
      P.boundaryFiberedIndexEquiv
  let splitBoundary :
      (P.BoundaryFiberedIndex → Value) ≃ᵐ
        P.BoundaryConfiguration Value ×
          ((P.PositiveEdge ⊕ P.PositiveEdge) → Value) :=
    MeasurableEquiv.sumPiEquivProdPi
      (fun _ : P.FixedEdge ⊕ (P.PositiveEdge ⊕ P.PositiveEdge) => Value)
  let splitHalves :
      ((P.PositiveEdge ⊕ P.PositiveEdge) → Value) ≃ᵐ
        P.OpenHalfConfiguration Value × P.OpenHalfConfiguration Value :=
    MeasurableEquiv.sumPiEquivProdPi
      (fun _ : P.PositiveEdge ⊕ P.PositiveEdge => Value)
  have hReindex :
      MeasurePreserving reindex
        (Measure.pi fun _ : Edge => mu)
        (Measure.pi fun _ : P.BoundaryFiberedIndex => mu) := by
    simpa [reindex] using
      (measurePreserving_piCongrLeft
        (α := fun _ : P.BoundaryFiberedIndex => Value)
        (fun _ : P.BoundaryFiberedIndex => mu)
        P.boundaryFiberedIndexEquiv)
  have hSplitBoundary :
      MeasurePreserving splitBoundary
        (Measure.pi fun _ : P.BoundaryFiberedIndex => mu)
        ((Measure.pi fun _ : P.FixedEdge => mu).prod
          (Measure.pi fun _ : P.PositiveEdge ⊕ P.PositiveEdge => mu)) := by
    simpa [splitBoundary] using
      (measurePreserving_sumPiEquivProdPi
        (X := fun _ : P.FixedEdge ⊕ (P.PositiveEdge ⊕ P.PositiveEdge) => Value)
        (fun _ => mu))
  have hSplitHalves :
      MeasurePreserving splitHalves
        (Measure.pi fun _ : P.PositiveEdge ⊕ P.PositiveEdge => mu)
        ((Measure.pi fun _ : P.PositiveEdge => mu).prod
          (Measure.pi fun _ : P.PositiveEdge => mu)) := by
    simpa [splitHalves] using
      (measurePreserving_sumPiEquivProdPi
        (X := fun _ : P.PositiveEdge ⊕ P.PositiveEdge => Value)
        (fun _ => mu))
  have hBoundaryId :
      MeasurePreserving
        (MeasurableEquiv.refl (P.BoundaryConfiguration Value))
        (Measure.pi fun _ : P.FixedEdge => mu)
        (Measure.pi fun _ : P.FixedEdge => mu) :=
    ⟨measurable_id, Measure.map_id⟩
  have hFinal := hBoundaryId.prod hSplitHalves
  simpa [boundaryFiberedMeasurableEquiv, reindex, splitBoundary, splitHalves] using
    hFinal.comp (hSplitBoundary.comp hReindex)

/-- Pushforward form of product-measure boundary factorization. -/
theorem map_boundaryFiberedCoordinates_pi
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    (Value : Type v)
    [MeasurableSpace Value]
    (mu : Measure Value)
    [SigmaFinite mu] :
    Measure.map (P.boundaryFiberedCoordinates Value)
        (Measure.pi fun _ : Edge => mu) =
      (Measure.pi fun _ : P.FixedEdge => mu).prod
        ((Measure.pi fun _ : P.PositiveEdge => mu).prod
          (Measure.pi fun _ : P.PositiveEdge => mu)) := by
  rw [← P.boundaryFiberedMeasurableEquiv_coe Value]
  exact (P.measurePreserving_boundaryFiberedMeasurableEquiv Value mu).map_eq

/-- Canonical boundary-fibered measure-factorization package for a finite
product of one sigma-finite base measure. -/
noncomputable def piBoundaryFiberedMeasureFactorization
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    (Value : Type v)
    [MeasurableSpace Value]
    (mu : Measure Value)
    [SigmaFinite mu] :
    P.BoundaryFiberedMeasureFactorization Value where
  fullMeasure := Measure.pi fun _ : Edge => mu
  boundaryMeasure := Measure.pi fun _ : P.FixedEdge => mu
  halfMeasure := Measure.pi fun _ : P.PositiveEdge => mu
  boundaryMeasure_sfinite := inferInstance
  halfMeasure_sfinite := inferInstance
  coordinates_aemeasurable := by
    rw [← P.boundaryFiberedMeasurableEquiv_coe Value]
    exact (P.boundaryFiberedMeasurableEquiv Value).measurable.aemeasurable
  map_coordinates_fullMeasure :=
    P.map_boundaryFiberedCoordinates_pi Value mu

end FiniteInvolutiveEdgeOrbitPartition

end

end MathlibAnalytic
end MGAP4D
