import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonOSBochnerGram

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- A half-lattice kernel decomposition together with a Hilbert feature
factorization of the crossing-plane kernel.

This separates the two model-specific steps in the compact `SU(N)`
reflection-positivity calculation:

1. split the Wilson Gibbs integral into a positive/negative half-lattice kernel
   quadratic form;
2. identify the crossing kernel with an inner product of Peter--Weyl feature
   vectors.
-/
structure PhysicalYangMillsOrientedWilsonOSKernelFeatureCertificate
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L)) where
  HalfConfiguration : Type
  [halfMeasurableSpace : MeasurableSpace HalfConfiguration]
  halfMeasure : Measure HalfConfiguration
  FeatureHilbert : Type
  [featureNormedAddCommGroup : NormedAddCommGroup FeatureHilbert]
  [featureInnerProductSpace : InnerProductSpace ℝ FeatureHilbert]
  [featureCompleteSpace : CompleteSpace FeatureHilbert]
  amplitude : ℕ → D.positiveTimeSubalgebra → HalfConfiguration → ℝ
  crossingKernel : ℕ → HalfConfiguration → HalfConfiguration → ℝ
  feature : ℕ → HalfConfiguration → FeatureHilbert
  weightedFeature_integrable :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra),
      Integrable
        (fun x => amplitude n F x • feature n x)
        halfMeasure
  pullbackForm_eq_kernelQuadratic :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra),
      D.orientedWilsonPullbackForm G L n F =
        ∫ x, ∫ y,
          amplitude n F x * crossingKernel n x y * amplitude n F y
          ∂halfMeasure ∂halfMeasure
  crossingKernel_eq_inner :
    ∀ (n : ℕ) (x y : HalfConfiguration),
      crossingKernel n x y = inner ℝ (feature n x) (feature n y)

attribute [instance]
  PhysicalYangMillsOrientedWilsonOSKernelFeatureCertificate.halfMeasurableSpace
  PhysicalYangMillsOrientedWilsonOSKernelFeatureCertificate.featureNormedAddCommGroup
  PhysicalYangMillsOrientedWilsonOSKernelFeatureCertificate.featureInnerProductSpace
  PhysicalYangMillsOrientedWilsonOSKernelFeatureCertificate.featureCompleteSpace

/-- A kernel/feature certificate generates the Bochner Gram certificate. -/
noncomputable def
    PhysicalYangMillsOrientedWilsonOSKernelFeatureCertificate.toBochnerGramCertificate
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E.PhysicalGaugeAction}
    {L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L)}
    (C : PhysicalYangMillsOrientedWilsonOSKernelFeatureCertificate G L D) :
    PhysicalYangMillsOrientedWilsonOSBochnerGramCertificate G L D where
  HalfConfiguration := C.HalfConfiguration
  halfMeasure := C.halfMeasure
  FeatureHilbert := C.FeatureHilbert
  amplitude := C.amplitude
  feature := C.feature
  weightedFeature_integrable := C.weightedFeature_integrable
  pullbackForm_eq_iterated_inner n F := by
    rw [C.pullbackForm_eq_kernelQuadratic]
    apply integral_congr_ae
    filter_upwards [] with x
    apply integral_congr_ae
    filter_upwards [] with y
    rw [C.crossingKernel_eq_inner]
    simp only [real_inner_smul_left, real_inner_smul_right]
    ring

/-- The kernel decomposition and its Hilbert feature factorization imply
reflection positivity at every physical lattice scale. -/
theorem physical_yang_mills_oriented_kernelFeature_approximating_reflectionPositive
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L))
    (C : PhysicalYangMillsOrientedWilsonOSKernelFeatureCertificate G L D)
    (n : ℕ) :
    D.WeakStarReflectionPositive
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState
        (G.toSymmetryLimit L) n) :=
  physical_yang_mills_oriented_bochnerGram_approximating_reflectionPositive
    G L D C.toBochnerGramCertificate n

/-- A half-lattice Wilson kernel with a Peter--Weyl Hilbert feature
factorization yields continuum Osterwalder--Schrader reflection positivity. -/
theorem physical_yang_mills_oriented_kernelFeature_continuum_reflectionPositive
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L))
    (C : PhysicalYangMillsOrientedWilsonOSKernelFeatureCertificate G L D) :
    D.WeakStarReflectionPositive
      (physicalYangMillsContinuumGaugeInvariantWeakStarState
        (G.toSymmetryLimit L)) :=
  physical_yang_mills_oriented_bochnerGram_continuum_reflectionPositive
    G L D C.toBochnerGramCertificate

end

end MathlibAnalytic
end MGAP4D
