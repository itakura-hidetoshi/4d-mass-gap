import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonOSKernelFeature

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The geometric and measure-theoretic half-lattice decomposition of the
actual compact Wilson pullback form.

This structure contains no positivity or representation-theoretic assumption.
It isolates the exact change of variables and Wilson-action splitting that
turn the original compact Gibbs integral into a quadratic kernel integral. -/
structure PhysicalYangMillsOrientedWilsonOSHalfLatticeDecomposition
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L)) where
  HalfConfiguration : Type
  [halfMeasurableSpace : MeasurableSpace HalfConfiguration]
  halfMeasure : Measure HalfConfiguration
  amplitude : ℕ → D.positiveTimeSubalgebra → HalfConfiguration → ℝ
  crossingKernel : ℕ → HalfConfiguration → HalfConfiguration → ℝ
  pullbackForm_eq_kernelQuadratic :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra),
      D.orientedWilsonPullbackForm G L n F =
        ∫ x, ∫ y,
          amplitude n F x * crossingKernel n x y * amplitude n F y
          ∂halfMeasure ∂halfMeasure

attribute [instance]
  PhysicalYangMillsOrientedWilsonOSHalfLatticeDecomposition.halfMeasurableSpace

/-- The representation-theoretic input for a fixed half-lattice decomposition.

For compact `SU(N)`, `feature` is intended to collect square roots of the
nonnegative Wilson character coefficients times Peter--Weyl matrix
coefficients. -/
structure PhysicalYangMillsOrientedWilsonOSPeterWeylFeature
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E.PhysicalGaugeAction}
    {L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L)}
    (H : PhysicalYangMillsOrientedWilsonOSHalfLatticeDecomposition G L D) where
  FeatureHilbert : Type
  [featureNormedAddCommGroup : NormedAddCommGroup FeatureHilbert]
  [featureInnerProductSpace : InnerProductSpace ℝ FeatureHilbert]
  [featureCompleteSpace : CompleteSpace FeatureHilbert]
  feature : ℕ → H.HalfConfiguration → FeatureHilbert
  weightedFeature_integrable :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra),
      Integrable
        (fun x => H.amplitude n F x • feature n x)
        H.halfMeasure
  crossingKernel_eq_inner :
    ∀ (n : ℕ) (x y : H.HalfConfiguration),
      H.crossingKernel n x y = inner ℝ (feature n x) (feature n y)

attribute [instance]
  PhysicalYangMillsOrientedWilsonOSPeterWeylFeature.featureNormedAddCommGroup
  PhysicalYangMillsOrientedWilsonOSPeterWeylFeature.featureInnerProductSpace
  PhysicalYangMillsOrientedWilsonOSPeterWeylFeature.featureCompleteSpace

/-- Combine the independent half-lattice decomposition and Peter--Weyl feature
factorization into the kernel-feature certificate. -/
noncomputable def
    PhysicalYangMillsOrientedWilsonOSPeterWeylFeature.toKernelFeatureCertificate
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E.PhysicalGaugeAction}
    {L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L)}
    {H : PhysicalYangMillsOrientedWilsonOSHalfLatticeDecomposition G L D}
    (P : PhysicalYangMillsOrientedWilsonOSPeterWeylFeature H) :
    PhysicalYangMillsOrientedWilsonOSKernelFeatureCertificate G L D where
  HalfConfiguration := H.HalfConfiguration
  halfMeasure := H.halfMeasure
  FeatureHilbert := P.FeatureHilbert
  amplitude := H.amplitude
  crossingKernel := H.crossingKernel
  feature := P.feature
  weightedFeature_integrable := P.weightedFeature_integrable
  pullbackForm_eq_kernelQuadratic := H.pullbackForm_eq_kernelQuadratic
  crossingKernel_eq_inner := P.crossingKernel_eq_inner

/-- Geometry/measure splitting plus the Peter--Weyl feature theorem proves
reflection positivity of every physical lattice state. -/
theorem physical_yang_mills_oriented_halfLattice_peterWeyl_approximating_reflectionPositive
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L))
    (H : PhysicalYangMillsOrientedWilsonOSHalfLatticeDecomposition G L D)
    (P : PhysicalYangMillsOrientedWilsonOSPeterWeylFeature H)
    (n : ℕ) :
    D.WeakStarReflectionPositive
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState
        (G.toSymmetryLimit L) n) :=
  physical_yang_mills_oriented_kernelFeature_approximating_reflectionPositive
    G L D P.toKernelFeatureCertificate n

/-- The concrete two-part finite-volume input implies continuum
Osterwalder--Schrader reflection positivity. -/
theorem physical_yang_mills_oriented_halfLattice_peterWeyl_continuum_reflectionPositive
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L))
    (H : PhysicalYangMillsOrientedWilsonOSHalfLatticeDecomposition G L D)
    (P : PhysicalYangMillsOrientedWilsonOSPeterWeylFeature H) :
    D.WeakStarReflectionPositive
      (physicalYangMillsContinuumGaugeInvariantWeakStarState
        (G.toSymmetryLimit L)) :=
  physical_yang_mills_oriented_kernelFeature_continuum_reflectionPositive
    G L D P.toKernelFeatureCertificate

end

end MathlibAnalytic
end MGAP4D
