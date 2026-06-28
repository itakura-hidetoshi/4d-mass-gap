import MGAP4D.MathlibAnalytic.FiniteInvolutiveEdgeBoundaryFiberedBochnerFactorization
import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonOSBoundaryFiberedBochnerGram

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

universe v w

/-- Concrete coordinate-to-Bochner bridge for a finite Wilson reflection.

This structure packages the exact full-configuration coordinate equivalence,
the pushforward of the full finite-volume measure to shared boundary data and
two open halves, and the boundary-dependent Hilbert feature whose Gram kernel
is the reflected Wilson observable. -/
structure PhysicalYangMillsOrientedWilsonOSBoundaryFiberedCoordinateData
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L))
    (Edge : Type)
    [edgeFintype : Fintype Edge]
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    (Value : Type v)
    [valueMeasurableSpace : MeasurableSpace Value] where
  measureFactorization :
    P.BoundaryFiberedMeasureFactorization Value
  FeatureHilbert : Type w
  [featureNormedAddCommGroup : NormedAddCommGroup FeatureHilbert]
  [featureInnerProductSpace : InnerProductSpace ℝ FeatureHilbert]
  [featureCompleteSpace : CompleteSpace FeatureHilbert]
  weightedFeature :
    ℕ → D.positiveTimeSubalgebra →
      P.BoundaryConfiguration Value →
        P.OpenHalfConfiguration Value → FeatureHilbert
  weightedFeature_integrable :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra)
      (b : P.BoundaryConfiguration Value),
      Integrable (weightedFeature n F b)
        measureFactorization.halfMeasure
  coordinateKernel_integrable :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra),
      Integrable
        (fun z : P.BoundaryConfiguration Value ×
            (P.OpenHalfConfiguration Value × P.OpenHalfConfiguration Value) =>
          inner ℝ
            (weightedFeature n F z.1 z.2.1)
            (weightedFeature n F z.1 z.2.2))
        (measureFactorization.boundaryMeasure.prod
          (measureFactorization.halfMeasure.prod
            measureFactorization.halfMeasure))
  fiberKernel_integrable :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra)
      (b : P.BoundaryConfiguration Value),
      Integrable
        (fun z : P.OpenHalfConfiguration Value ×
            P.OpenHalfConfiguration Value =>
          inner ℝ
            (weightedFeature n F b z.1)
            (weightedFeature n F b z.2))
        (measureFactorization.halfMeasure.prod
          measureFactorization.halfMeasure)
  boundaryMomentNormSq_integrable :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra),
      Integrable
        (fun b : P.BoundaryConfiguration Value =>
          ‖∫ x, weightedFeature n F b x
              ∂measureFactorization.halfMeasure‖ ^ 2)
        measureFactorization.boundaryMeasure
  pullbackForm_eq_fullCoordinateGram :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra),
      D.orientedWilsonPullbackForm G L n F =
        ∫ U,
          inner ℝ
            (weightedFeature n F
              (P.boundaryFiberedCoordinates Value U).1
              (P.boundaryFiberedCoordinates Value U).2.1)
            (weightedFeature n F
              (P.boundaryFiberedCoordinates Value U).1
              (P.boundaryFiberedCoordinates Value U).2.2)
          ∂measureFactorization.fullMeasure

attribute [instance]
  PhysicalYangMillsOrientedWilsonOSBoundaryFiberedCoordinateData.featureNormedAddCommGroup
  PhysicalYangMillsOrientedWilsonOSBoundaryFiberedCoordinateData.featureInnerProductSpace
  PhysicalYangMillsOrientedWilsonOSBoundaryFiberedCoordinateData.featureCompleteSpace

/-- Exact transport of the physical pullback form to a boundary-conditioned
iterated Hilbert Gram integral. -/
theorem PhysicalYangMillsOrientedWilsonOSBoundaryFiberedCoordinateData.pullbackForm_eq_boundary_iterated_inner
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E.PhysicalGaugeAction}
    {L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L)}
    {Edge : Type}
    [Fintype Edge]
    {P : FiniteInvolutiveEdgeOrbitPartition Edge}
    {Value : Type v}
    [MeasurableSpace Value]
    (C : PhysicalYangMillsOrientedWilsonOSBoundaryFiberedCoordinateData
      G L D Edge P Value)
    (n : ℕ)
    (F : D.positiveTimeSubalgebra) :
    D.orientedWilsonPullbackForm G L n F =
      ∫ b, ∫ x, ∫ y,
        inner ℝ
          (C.weightedFeature n F b x)
          (C.weightedFeature n F b y)
        ∂C.measureFactorization.halfMeasure
        ∂C.measureFactorization.halfMeasure
        ∂C.measureFactorization.boundaryMeasure := by
  rw [C.pullbackForm_eq_fullCoordinateGram n F]
  exact C.measureFactorization.integral_pullback_eq_boundary_half_half
    (fun z =>
      inner ℝ
        (C.weightedFeature n F z.1 z.2.1)
        (C.weightedFeature n F z.1 z.2.2))
    (C.coordinateKernel_integrable n F)
    (C.fiberKernel_integrable n F)

/-- Convert exact finite boundary coordinates and their measure transport into
the abstract boundary-fibered Bochner Gram certificate. -/
noncomputable def
    PhysicalYangMillsOrientedWilsonOSBoundaryFiberedCoordinateData.toBoundaryFiberedBochnerGramCertificate
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E.PhysicalGaugeAction}
    {L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L)}
    {Edge : Type}
    [Fintype Edge]
    {P : FiniteInvolutiveEdgeOrbitPartition Edge}
    {Value : Type v}
    [MeasurableSpace Value]
    (C : PhysicalYangMillsOrientedWilsonOSBoundaryFiberedCoordinateData
      G L D Edge P Value) :
    PhysicalYangMillsOrientedWilsonOSBoundaryFiberedBochnerGramCertificate
      G L D where
  BoundaryConfiguration := P.BoundaryConfiguration Value
  boundaryMeasurableSpace := inferInstance
  boundaryMeasure := C.measureFactorization.boundaryMeasure
  HalfConfiguration := P.OpenHalfConfiguration Value
  halfMeasurableSpace := inferInstance
  halfMeasure := fun _ => C.measureFactorization.halfMeasure
  FeatureHilbert := C.FeatureHilbert
  featureNormedAddCommGroup := C.featureNormedAddCommGroup
  featureInnerProductSpace := C.featureInnerProductSpace
  featureCompleteSpace := C.featureCompleteSpace
  weightedFeature := C.weightedFeature
  weightedFeature_integrable := C.weightedFeature_integrable
  boundaryMomentNormSq_integrable :=
    C.boundaryMomentNormSq_integrable
  pullbackForm_eq_boundary_iterated_inner :=
    C.pullbackForm_eq_boundary_iterated_inner

/-- Exact boundary-fibered coordinates, measure transport, and a conditional
Hilbert feature prove reflection positivity of every finite approximating
Wilson state. -/
theorem physical_yang_mills_oriented_boundaryFiberedCoordinates_approximating_reflectionPositive
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L))
    {Edge : Type}
    [Fintype Edge]
    {P : FiniteInvolutiveEdgeOrbitPartition Edge}
    {Value : Type v}
    [MeasurableSpace Value]
    (C : PhysicalYangMillsOrientedWilsonOSBoundaryFiberedCoordinateData
      G L D Edge P Value)
    (n : ℕ) :
    D.WeakStarReflectionPositive
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState
        (G.toSymmetryLimit L) n) :=
  physical_yang_mills_oriented_boundaryFiberedBochnerGram_approximating_reflectionPositive
    G L D C.toBoundaryFiberedBochnerGramCertificate n

/-- The same concrete boundary-coordinate package transfers reflection
positivity to the continuum weak-star state. -/
theorem physical_yang_mills_oriented_boundaryFiberedCoordinates_continuum_reflectionPositive
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L))
    {Edge : Type}
    [Fintype Edge]
    {P : FiniteInvolutiveEdgeOrbitPartition Edge}
    {Value : Type v}
    [MeasurableSpace Value]
    (C : PhysicalYangMillsOrientedWilsonOSBoundaryFiberedCoordinateData
      G L D Edge P Value) :
    D.WeakStarReflectionPositive
      (physicalYangMillsContinuumGaugeInvariantWeakStarState
        (G.toSymmetryLimit L)) :=
  physical_yang_mills_oriented_boundaryFiberedBochnerGram_continuum_reflectionPositive
    G L D C.toBoundaryFiberedBochnerGramCertificate

end

end MathlibAnalytic
end MGAP4D
