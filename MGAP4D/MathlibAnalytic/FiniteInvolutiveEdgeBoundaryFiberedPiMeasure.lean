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

/-- Product measure on the reflection-fixed boundary edge sector. -/
noncomputable def boundaryPiMeasure
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    {Value : Type v} [MeasurableSpace Value]
    (μ : Measure Value) : Measure (P.BoundaryConfiguration Value) :=
  Measure.pi (fun _ : P.FixedEdge => μ)

/-- Product measure on one selected open half-lattice. -/
noncomputable def openHalfPiMeasure
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    {Value : Type v} [MeasurableSpace Value]
    (μ : Measure Value) : Measure (P.OpenHalfConfiguration Value) :=
  Measure.pi (fun _ : P.PositiveEdge => μ)

/-- Canonical measurable coordinate equivalence obtained by reindexing the full
finite product by the fixed/positive/negative orbit decomposition and then
splitting the two sum-indexed function spaces. -/
noncomputable def boundaryFiberedPiMeasurableEquiv
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    (Value : Type v) [MeasurableSpace Value] :
    (Edge → Value) ≃ᵐ
      P.BoundaryConfiguration Value ×
        (P.OpenHalfConfiguration Value × P.OpenHalfConfiguration Value) :=
  (MeasurableEquiv.piCongrLeft
      (fun _ : P.BoundaryFiberedIndex => Value)
      P.boundaryFiberedIndexEquiv).trans
    ((MeasurableEquiv.sumPiEquivProdPi
        (fun _ : P.BoundaryFiberedIndex => Value)).trans
      ((MeasurableEquiv.refl (P.BoundaryConfiguration Value)).prodCongr
        (MeasurableEquiv.sumPiEquivProdPi
          (fun _ : P.PositiveEdge ⊕ P.PositiveEdge => Value))))

/-- The canonical measurable product decomposition is pointwise the same map as
the previously constructed geometric boundary-fibered coordinates. -/
theorem boundaryFiberedPiMeasurableEquiv_apply
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    (Value : Type v) [MeasurableSpace Value]
    (A : Edge → Value) :
    P.boundaryFiberedPiMeasurableEquiv Value A =
      P.boundaryFiberedCoordinates Value A := by
  apply Prod.ext
  · funext e
    simpa [boundaryFiberedPiMeasurableEquiv, boundaryFiberedCoordinates,
      boundaryRestriction] using
      (MeasurableEquiv.piCongrLeft_apply_apply
        (β := fun _ : P.BoundaryFiberedIndex => Value)
        P.boundaryFiberedIndexEquiv A e.1)
  · apply Prod.ext
    · funext e
      simpa [boundaryFiberedPiMeasurableEquiv, boundaryFiberedCoordinates,
        positiveRestriction] using
        (MeasurableEquiv.piCongrLeft_apply_apply
          (β := fun _ : P.BoundaryFiberedIndex => Value)
          P.boundaryFiberedIndexEquiv A e.1)
    · funext e
      simpa [boundaryFiberedPiMeasurableEquiv, boundaryFiberedCoordinates,
        negativeRestriction] using
        (MeasurableEquiv.piCongrLeft_apply_apply
          (β := fun _ : P.BoundaryFiberedIndex => Value)
          P.boundaryFiberedIndexEquiv A (P.reflection e.1))

/-- The full constant finite product measure is preserved by the canonical
boundary/open-half/open-half coordinate equivalence. -/
theorem boundaryFiberedPiMeasurableEquiv_measurePreserving
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    {Value : Type v} [MeasurableSpace Value]
    (μ : Measure Value) [SigmaFinite μ] :
    MeasurePreserving (P.boundaryFiberedPiMeasurableEquiv Value)
      (Measure.pi (fun _ : Edge => μ))
      ((P.boundaryPiMeasure μ).prod
        ((P.openHalfPiMeasure μ).prod (P.openHalfPiMeasure μ))) := by
  letI : SFinite (P.boundaryPiMeasure μ) := by
    unfold boundaryPiMeasure
    infer_instance
  let reindex := MeasurableEquiv.piCongrLeft
    (fun _ : P.BoundaryFiberedIndex => Value)
    P.boundaryFiberedIndexEquiv
  let splitOuter := MeasurableEquiv.sumPiEquivProdPi
    (fun _ : P.BoundaryFiberedIndex => Value)
  let splitInner := MeasurableEquiv.sumPiEquivProdPi
    (fun _ : P.PositiveEdge ⊕ P.PositiveEdge => Value)
  let splitNested :=
    (MeasurableEquiv.refl (P.BoundaryConfiguration Value)).prodCongr splitInner
  have hReindex :
      MeasurePreserving reindex
        (Measure.pi (fun _ : Edge => μ))
        (Measure.pi (fun _ : P.BoundaryFiberedIndex => μ)) := by
    exact MeasureTheory.measurePreserving_piCongrLeft
      (fun _ : P.BoundaryFiberedIndex => μ)
      P.boundaryFiberedIndexEquiv
  have hOuter :
      MeasurePreserving splitOuter
        (Measure.pi (fun _ : P.BoundaryFiberedIndex => μ))
        ((P.boundaryPiMeasure μ).prod
          (Measure.pi (fun _ : P.PositiveEdge ⊕ P.PositiveEdge => μ))) := by
    simpa [boundaryPiMeasure] using
      (MeasureTheory.measurePreserving_sumPiEquivProdPi
        (fun _ : P.BoundaryFiberedIndex => μ))
  have hInner :
      MeasurePreserving splitInner
        (Measure.pi (fun _ : P.PositiveEdge ⊕ P.PositiveEdge => μ))
        ((P.openHalfPiMeasure μ).prod (P.openHalfPiMeasure μ)) := by
    simpa [openHalfPiMeasure] using
      (MeasureTheory.measurePreserving_sumPiEquivProdPi
        (fun _ : P.PositiveEdge ⊕ P.PositiveEdge => μ))
  have hNested :
      MeasurePreserving splitNested
        ((P.boundaryPiMeasure μ).prod
          (Measure.pi (fun _ : P.PositiveEdge ⊕ P.PositiveEdge => μ)))
        ((P.boundaryPiMeasure μ).prod
          ((P.openHalfPiMeasure μ).prod (P.openHalfPiMeasure μ))) := by
    simpa [splitNested] using
      (MeasurePreserving.id (P.boundaryPiMeasure μ)).prod hInner
  simpa [boundaryFiberedPiMeasurableEquiv, reindex, splitOuter,
    splitInner, splitNested] using
    (hReindex.trans hOuter).trans hNested

/-- Geometric boundary-fibered coordinates are measurable for the canonical
finite product measurable structures. -/
theorem boundaryFiberedCoordinates_measurable
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    (Value : Type v) [MeasurableSpace Value] :
    Measurable (P.boundaryFiberedCoordinates Value) := by
  have hfun :
      (P.boundaryFiberedPiMeasurableEquiv Value :
        (Edge → Value) →
          P.BoundaryConfiguration Value ×
            (P.OpenHalfConfiguration Value × P.OpenHalfConfiguration Value)) =
        P.boundaryFiberedCoordinates Value := by
    funext A
    exact P.boundaryFiberedPiMeasurableEquiv_apply Value A
  rw [← hfun]
  exact (P.boundaryFiberedPiMeasurableEquiv Value).measurable

/-- Exact pushforward of a constant finite product measure through the geometric
boundary-fibered coordinates. -/
theorem map_boundaryFiberedCoordinates_pi
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    {Value : Type v} [MeasurableSpace Value]
    (μ : Measure Value) [SigmaFinite μ] :
    Measure.map (P.boundaryFiberedCoordinates Value)
        (Measure.pi (fun _ : Edge => μ)) =
      (P.boundaryPiMeasure μ).prod
        ((P.openHalfPiMeasure μ).prod (P.openHalfPiMeasure μ)) := by
  have hfun :
      (P.boundaryFiberedPiMeasurableEquiv Value :
        (Edge → Value) →
          P.BoundaryConfiguration Value ×
            (P.OpenHalfConfiguration Value × P.OpenHalfConfiguration Value)) =
        P.boundaryFiberedCoordinates Value := by
    funext A
    exact P.boundaryFiberedPiMeasurableEquiv_apply Value A
  rw [← hfun]
  exact (P.boundaryFiberedPiMeasurableEquiv_measurePreserving μ).map_eq

/-- Canonical boundary-fibered measure factorization of a constant finite
product measure. -/
noncomputable def boundaryFiberedPiMeasureFactorization
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    {Value : Type v} [MeasurableSpace Value]
    (μ : Measure Value) [SigmaFinite μ] :
    P.BoundaryFiberedMeasureFactorization Value where
  fullMeasure := Measure.pi (fun _ : Edge => μ)
  boundaryMeasure := P.boundaryPiMeasure μ
  halfMeasure := P.openHalfPiMeasure μ
  boundaryMeasure_sfinite := by
    unfold boundaryPiMeasure
    infer_instance
  halfMeasure_sfinite := by
    unfold openHalfPiMeasure
    infer_instance
  coordinates_aemeasurable :=
    (P.boundaryFiberedCoordinates_measurable Value).aemeasurable
  map_coordinates_fullMeasure := P.map_boundaryFiberedCoordinates_pi μ

end FiniteInvolutiveEdgeOrbitPartition

end

end MathlibAnalytic
end MGAP4D
