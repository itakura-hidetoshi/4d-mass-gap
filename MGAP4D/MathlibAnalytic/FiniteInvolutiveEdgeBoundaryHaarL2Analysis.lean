import MGAP4D.MathlibAnalytic.FiniteInvolutiveEdgeBoundaryFiberedPiMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Basic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

namespace FiniteInvolutiveEdgeOrbitPartition

universe v

variable {Edge : Type} [Fintype Edge]

/-- The canonical projection from a full edge configuration to its
reflection-fixed boundary coordinates, expressed through the exact measurable
boundary/open-half/open-half reindexing equivalence. -/
noncomputable def boundaryHaarProjection
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    (Value : Type v) [MeasurableSpace Value] :
    (Edge → Value) → P.BoundaryConfiguration Value :=
  fun A => (P.boundaryFiberedPiMeasurableEquiv Value A).1

/-- The canonical measurable-equivalence projection is pointwise the geometric
boundary component of the previously constructed boundary-fibered coordinates. -/
theorem boundaryHaarProjection_eq_boundaryFiberedCoordinates_fst
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    (Value : Type v) [MeasurableSpace Value]
    (A : Edge → Value) :
    P.boundaryHaarProjection Value A =
      (P.boundaryFiberedCoordinates Value A).1 := by
  unfold boundaryHaarProjection
  rw [P.boundaryFiberedPiMeasurableEquiv_apply Value A]

/-- For a probability law on each edge value, projection of the full product
law to the reflection-fixed edge sector preserves exactly the boundary product
law.  The two open-half factors disappear because their product law is again a
probability measure. -/
theorem boundaryHaarProjection_measurePreserving
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    {Value : Type v} [MeasurableSpace Value]
    (μ : Measure Value) [SigmaFinite μ] [IsProbabilityMeasure μ] :
    MeasurePreserving (P.boundaryHaarProjection Value)
      (Measure.pi (fun _ : Edge => μ))
      (P.boundaryPiMeasure μ) := by
  letI : SFinite (P.openHalfPiMeasure μ) := by
    unfold openHalfPiMeasure
    infer_instance
  letI : IsProbabilityMeasure (P.openHalfPiMeasure μ) := by
    unfold openHalfPiMeasure
    infer_instance
  have hcoordinates :=
    P.boundaryFiberedPiMeasurableEquiv_measurePreserving μ
  have hprojection :
      MeasurePreserving Prod.fst
        ((P.boundaryPiMeasure μ).prod
          ((P.openHalfPiMeasure μ).prod (P.openHalfPiMeasure μ)))
        (P.boundaryPiMeasure μ) :=
    measurePreserving_fst
  simpa [boundaryHaarProjection, Function.comp_def] using
    hprojection.comp hcoordinates

/-- The standard real boundary `L²` space for a finite involutive edge
partition and a one-edge probability law. -/
abbrev BoundaryHaarL2
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    {Value : Type v} [MeasurableSpace Value]
    (μ : Measure Value) : Type v :=
  Lp ℝ 2 (P.boundaryPiMeasure μ)

/-- The standard real full-configuration `L²` space for a finite product edge
law. -/
abbrev ConfigurationHaarL2
    (Edge : Type) [Fintype Edge]
    {Value : Type v} [MeasurableSpace Value]
    (μ : Measure Value) : Type v :=
  Lp ℝ 2 (Measure.pi (fun _ : Edge => μ))

/-- Pullback along the genuine boundary projection gives a canonical linear
isometric embedding from boundary Haar `L²` into full-configuration Haar
`L²`. -/
noncomputable def boundaryHaarL2Analysis
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    {Value : Type v} [MeasurableSpace Value]
    (μ : Measure Value) [SigmaFinite μ] [IsProbabilityMeasure μ] :
    P.BoundaryHaarL2 μ →ₗᵢ[ℝ] ConfigurationHaarL2 Edge μ :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
    (P.boundaryHaarProjection Value)
    (P.boundaryHaarProjection_measurePreserving μ)

/-- The configuration-space representative of boundary analysis is the
boundary `L²` representative evaluated on the actual boundary restriction. -/
theorem boundaryHaarL2Analysis_coeFn
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    {Value : Type v} [MeasurableSpace Value]
    (μ : Measure Value) [SigmaFinite μ] [IsProbabilityMeasure μ]
    (f : P.BoundaryHaarL2 μ) :
    P.boundaryHaarL2Analysis μ f =ᵐ[Measure.pi (fun _ : Edge => μ)]
      fun A => f (P.boundaryFiberedCoordinates Value A).1 := by
  filter_upwards [MeasureTheory.Lp.coeFn_compMeasurePreserving
    f (P.boundaryHaarProjection_measurePreserving μ)] with A hA
  rw [hA, Function.comp_apply,
    P.boundaryHaarProjection_eq_boundaryFiberedCoordinates_fst Value A]

end FiniteInvolutiveEdgeOrbitPartition

end

end MathlibAnalytic
end MGAP4D
