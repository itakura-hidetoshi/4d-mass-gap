import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonOSBochnerGram

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Boundary-fibered Bochner Gram data for a Wilson reflection with fixed-plane
variables shared by the positive and negative halves.

For each boundary configuration `b`, the two open half-lattices are integrated
against the same conditional half measure `halfMeasure b`.  The reflected
quadratic form is therefore a boundary integral of conditional Hilbert Gram
forms, rather than a single unconditional product integral.  This is the
correct abstract shape when spatial links on the reflection-fixed time planes
are shared variables and cannot be duplicated into two independent Haar
coordinates. -/
structure PhysicalYangMillsOrientedWilsonOSBoundaryFiberedBochnerGramCertificate
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L)) where
  BoundaryConfiguration : Type
  [boundaryMeasurableSpace : MeasurableSpace BoundaryConfiguration]
  boundaryMeasure : Measure BoundaryConfiguration
  HalfConfiguration : Type
  [halfMeasurableSpace : MeasurableSpace HalfConfiguration]
  halfMeasure : BoundaryConfiguration → Measure HalfConfiguration
  FeatureHilbert : Type
  [featureNormedAddCommGroup : NormedAddCommGroup FeatureHilbert]
  [featureInnerProductSpace : InnerProductSpace ℝ FeatureHilbert]
  [featureCompleteSpace : CompleteSpace FeatureHilbert]
  weightedFeature :
    ℕ → D.positiveTimeSubalgebra → BoundaryConfiguration →
      HalfConfiguration → FeatureHilbert
  weightedFeature_integrable :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra)
      (b : BoundaryConfiguration),
      Integrable (weightedFeature n F b) (halfMeasure b)
  boundaryMomentNormSq_integrable :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra),
      Integrable
        (fun b : BoundaryConfiguration =>
          ‖∫ x, weightedFeature n F b x ∂halfMeasure b‖ ^ 2)
        boundaryMeasure
  pullbackForm_eq_boundary_iterated_inner :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra),
      D.orientedWilsonPullbackForm G L n F =
        ∫ b, ∫ x, ∫ y,
          inner ℝ
            (weightedFeature n F b x)
            (weightedFeature n F b y)
          ∂halfMeasure b ∂halfMeasure b ∂boundaryMeasure

attribute [instance]
  PhysicalYangMillsOrientedWilsonOSBoundaryFiberedBochnerGramCertificate.boundaryMeasurableSpace
  PhysicalYangMillsOrientedWilsonOSBoundaryFiberedBochnerGramCertificate.halfMeasurableSpace
  PhysicalYangMillsOrientedWilsonOSBoundaryFiberedBochnerGramCertificate.featureNormedAddCommGroup
  PhysicalYangMillsOrientedWilsonOSBoundaryFiberedBochnerGramCertificate.featureInnerProductSpace
  PhysicalYangMillsOrientedWilsonOSBoundaryFiberedBochnerGramCertificate.featureCompleteSpace

/-- The conditional Bochner moment over the open positive half-lattice at a
fixed boundary configuration. -/
noncomputable def
    PhysicalYangMillsOrientedWilsonOSBoundaryFiberedBochnerGramCertificate.boundaryMoment
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E.PhysicalGaugeAction}
    {L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L)}
    (C : PhysicalYangMillsOrientedWilsonOSBoundaryFiberedBochnerGramCertificate
      G L D)
    (n : ℕ)
    (F : D.positiveTimeSubalgebra)
    (b : C.BoundaryConfiguration) : C.FeatureHilbert :=
  ∫ x, C.weightedFeature n F b x ∂C.halfMeasure b

/-- Fiberwise Bochner Gram reduction turns the boundary-conditioned iterated
inner product into the boundary integral of squared conditional moments. -/
theorem physical_yang_mills_oriented_boundaryFiberedBochnerGram_pullbackForm_eq_boundary_norm_sq
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L))
    (C : PhysicalYangMillsOrientedWilsonOSBoundaryFiberedBochnerGramCertificate
      G L D)
    (n : ℕ)
    (F : D.positiveTimeSubalgebra) :
    D.orientedWilsonPullbackForm G L n F =
      ∫ b, ‖C.boundaryMoment n F b‖ ^ 2 ∂C.boundaryMeasure := by
  rw [C.pullbackForm_eq_boundary_iterated_inner]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun b => by
    simpa [PhysicalYangMillsOrientedWilsonOSBoundaryFiberedBochnerGramCertificate.boundaryMoment] using
      iterated_integral_real_inner_eq_norm_integral_sq
        (C.halfMeasure b)
        (C.weightedFeature n F b)
        (C.weightedFeature_integrable n F b)

/-- A boundary-fibered Bochner Gram representation proves nonnegativity of the
actual compact Wilson pullback reflection form. -/
theorem physical_yang_mills_oriented_boundaryFiberedBochnerGram_pullbackForm_nonneg
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L))
    (C : PhysicalYangMillsOrientedWilsonOSBoundaryFiberedBochnerGramCertificate
      G L D)
    (n : ℕ)
    (F : D.positiveTimeSubalgebra) :
    0 ≤ D.orientedWilsonPullbackForm G L n F := by
  rw [physical_yang_mills_oriented_boundaryFiberedBochnerGram_pullbackForm_eq_boundary_norm_sq
    G L D C n F]
  exact integral_nonneg fun b => sq_nonneg ‖C.boundaryMoment n F b‖

/-- Forget the explicit boundary disintegration while retaining the generated
finite-volume pullback reflection positivity. -/
noncomputable def
    PhysicalYangMillsOrientedWilsonOSBoundaryFiberedBochnerGramCertificate.toPullbackCertificate
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E.PhysicalGaugeAction}
    {L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L)}
    (C : PhysicalYangMillsOrientedWilsonOSBoundaryFiberedBochnerGramCertificate
      G L D) :
    PhysicalYangMillsOrientedWilsonOSPullbackCertificate G L D where
  finiteReflectionPositive n F :=
    physical_yang_mills_oriented_boundaryFiberedBochnerGram_pullbackForm_nonneg
      G L D C n F

/-- Boundary-fibered Bochner Gram data make every approximating Wilson state
Osterwalder--Schrader reflection positive. -/
theorem physical_yang_mills_oriented_boundaryFiberedBochnerGram_approximating_reflectionPositive
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L))
    (C : PhysicalYangMillsOrientedWilsonOSBoundaryFiberedBochnerGramCertificate
      G L D)
    (n : ℕ) :
    D.WeakStarReflectionPositive
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState
        (G.toSymmetryLimit L) n) :=
  physical_yang_mills_oriented_pullback_approximating_reflectionPositive
    G L D C.toPullbackCertificate n

/-- Boundary-fibered finite-volume reflection positivity transfers through the
actual interpolation and Prokhorov weak limit to the continuum state. -/
theorem physical_yang_mills_oriented_boundaryFiberedBochnerGram_continuum_reflectionPositive
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L))
    (C : PhysicalYangMillsOrientedWilsonOSBoundaryFiberedBochnerGramCertificate
      G L D) :
    D.WeakStarReflectionPositive
      (physicalYangMillsContinuumGaugeInvariantWeakStarState
        (G.toSymmetryLimit L)) :=
  physical_yang_mills_oriented_pullback_continuum_reflectionPositive
    G L D C.toPullbackCertificate

end

end MathlibAnalytic
end MGAP4D
