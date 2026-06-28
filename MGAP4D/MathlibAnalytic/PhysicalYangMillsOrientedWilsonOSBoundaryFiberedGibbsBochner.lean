import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonBoundaryFiberedDensityBochner
import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonOSPullback

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

universe w

/-- A bundled real Hilbert space used by one lattice scale. -/
structure BoundaryFiberedScaleRealHilbertSpace where
  Carrier : Type w
  [normedAddCommGroup : NormedAddCommGroup Carrier]
  [innerProductSpace : InnerProductSpace ℝ Carrier]
  [completeSpace : CompleteSpace Carrier]

attribute [instance]
  BoundaryFiberedScaleRealHilbertSpace.normedAddCommGroup
  BoundaryFiberedScaleRealHilbertSpace.innerProductSpace
  BoundaryFiberedScaleRealHilbertSpace.completeSpace

/-- Scale-dependent boundary-fibered Gibbs Gram data for the actual physical
Wilson pullback forms.

Every selected lattice scale may have its own edge partition and Hilbert
feature space.  The only model-specific algebraic obligation is the pointwise
identity between the density-weighted reflected observable and the supplied
conditional Hilbert inner product. -/
structure PhysicalYangMillsOrientedWilsonOSBoundaryFiberedGibbsBochnerData
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L)) where
  partition :
    ∀ n, FiniteInvolutiveEdgeOrbitPartition
      (E.system (L.subsequence n)).base.geometry.Edge
  featureSpace : ℕ → BoundaryFiberedScaleRealHilbertSpace
  coordinateObservable :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra),
      (partition n).BoundaryConfiguration
          (E.system (L.subsequence n)).base.Gauge ×
        ((partition n).OpenHalfConfiguration
            (E.system (L.subsequence n)).base.Gauge ×
          (partition n).OpenHalfConfiguration
            (E.system (L.subsequence n)).base.Gauge) → ℝ
  weightedFeature :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra),
      (partition n).BoundaryConfiguration
          (E.system (L.subsequence n)).base.Gauge →
        (partition n).OpenHalfConfiguration
          (E.system (L.subsequence n)).base.Gauge →
            (featureSpace n).Carrier
  quadraticObservable_pullback_eq_coordinateObservable :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra)
      (U : (E.system (L.subsequence n)).base.Configuration),
      (((D.quadraticObservable F :
          physicalYangMillsGaugeInvariantObservableSubalgebra
            (G.toSymmetryLimit L)) :
        BoundedContinuousFunction (G.toSymmetryLimit L).Configuration ℝ)
          (E.interpolate (L.subsequence n) U)) =
        coordinateObservable n F
          ((partition n).boundaryFiberedCoordinates
            (E.system (L.subsequence n)).base.Gauge U)
  coordinateObservable_integrable :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra),
      Integrable (coordinateObservable n F)
        ((((partition n).boundaryPiMeasure
            (normalizedCompactHaar
              (E.system (L.subsequence n)).base.Gauge)).prod
          (((partition n).openHalfPiMeasure
              (normalizedCompactHaar
                (E.system (L.subsequence n)).base.Gauge)).prod
            ((partition n).openHalfPiMeasure
              (normalizedCompactHaar
                (E.system (L.subsequence n)).base.Gauge)))).withDensity
          ((E.system (L.subsequence n)).boundaryFiberedGibbsDensity
            (partition n)))
  weightedFeature_integrable :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra) b,
      Integrable (weightedFeature n F b)
        ((partition n).openHalfPiMeasure
          (normalizedCompactHaar
            (E.system (L.subsequence n)).base.Gauge))
  density_toReal_mul_coordinateObservable_eq_inner :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra) z,
      (((E.system (L.subsequence n)).boundaryFiberedGibbsDensity
        (partition n) z).toReal) * coordinateObservable n F z =
        inner ℝ
          (weightedFeature n F z.1 z.2.1)
          (weightedFeature n F z.1 z.2.2)
  kernel_integrable :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra),
      Integrable
        (fun z => inner ℝ
          (weightedFeature n F z.1 z.2.1)
          (weightedFeature n F z.1 z.2.2))
        (((partition n).boundaryPiMeasure
            (normalizedCompactHaar
              (E.system (L.subsequence n)).base.Gauge)).prod
          (((partition n).openHalfPiMeasure
              (normalizedCompactHaar
                (E.system (L.subsequence n)).base.Gauge)).prod
            ((partition n).openHalfPiMeasure
              (normalizedCompactHaar
                (E.system (L.subsequence n)).base.Gauge))))
  fiberKernel_integrable :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra) b,
      Integrable
        (fun z => inner ℝ
          (weightedFeature n F b z.1)
          (weightedFeature n F b z.2))
        (((partition n).openHalfPiMeasure
            (normalizedCompactHaar
              (E.system (L.subsequence n)).base.Gauge)).prod
          ((partition n).openHalfPiMeasure
            (normalizedCompactHaar
              (E.system (L.subsequence n)).base.Gauge)))

/-- The compact Wilson density-Bochner package generated at one selected
physical lattice scale. -/
noncomputable def
    PhysicalYangMillsOrientedWilsonOSBoundaryFiberedGibbsBochnerData.atScale
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E.PhysicalGaugeAction}
    {L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L)}
    (C : PhysicalYangMillsOrientedWilsonOSBoundaryFiberedGibbsBochnerData
      G L D)
    (n : ℕ)
    (F : D.positiveTimeSubalgebra) :
    ContinuousCompactOrientedGaugeWilsonBoundaryFiberedDensityBochnerData
      (E.system (L.subsequence n)) (C.partition n)
      (C.featureSpace n).Carrier where
  fullObservable := fun U =>
    (((D.quadraticObservable F :
        physicalYangMillsGaugeInvariantObservableSubalgebra
          (G.toSymmetryLimit L)) :
      BoundedContinuousFunction (G.toSymmetryLimit L).Configuration ℝ)
        (E.interpolate (L.subsequence n) U))
  coordinateObservable := C.coordinateObservable n F
  fullObservable_eq_coordinateObservable :=
    C.quadraticObservable_pullback_eq_coordinateObservable n F
  coordinateObservable_integrable :=
    C.coordinateObservable_integrable n F
  weightedFeature := C.weightedFeature n F
  weightedFeature_integrable := C.weightedFeature_integrable n F
  density_toReal_mul_coordinateObservable_eq_inner :=
    C.density_toReal_mul_coordinateObservable_eq_inner n F
  kernel_integrable := C.kernel_integrable n F
  fiberKernel_integrable := C.fiberKernel_integrable n F

/-- The physical Wilson pullback form at every selected scale is a boundary
integral of squared conditional Hilbert moments. -/
theorem physical_yang_mills_oriented_boundaryFiberedGibbsBochner_pullbackForm_eq_norm_sq
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L))
    (C : PhysicalYangMillsOrientedWilsonOSBoundaryFiberedGibbsBochnerData
      G L D)
    (n : ℕ)
    (F : D.positiveTimeSubalgebra) :
    D.orientedWilsonPullbackForm G L n F =
      ∫ b, ‖∫ x, C.weightedFeature n F b x
        ∂(C.partition n).openHalfPiMeasure
          (normalizedCompactHaar
            (E.system (L.subsequence n)).base.Gauge)‖ ^ 2
        ∂(C.partition n).boundaryPiMeasure
          (normalizedCompactHaar
            (E.system (L.subsequence n)).base.Gauge) := by
  unfold PhysicalYangMillsGaugeInvariantOSReflectionData.orientedWilsonPullbackForm
  exact continuous_compact_oriented_boundaryFiberedDensityBochner_integral_eq_norm_sq
    (C.atScale n F)

/-- Density-weighted boundary-fibered Gram data prove nonnegativity of every
finite physical Wilson pullback form. -/
theorem physical_yang_mills_oriented_boundaryFiberedGibbsBochner_pullbackForm_nonneg
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L))
    (C : PhysicalYangMillsOrientedWilsonOSBoundaryFiberedGibbsBochnerData
      G L D)
    (n : ℕ)
    (F : D.positiveTimeSubalgebra) :
    0 ≤ D.orientedWilsonPullbackForm G L n F := by
  rw [physical_yang_mills_oriented_boundaryFiberedGibbsBochner_pullbackForm_eq_norm_sq
    G L D C n F]
  exact integral_nonneg fun b => sq_nonneg ‖∫ x, C.weightedFeature n F b x
    ∂(C.partition n).openHalfPiMeasure
      (normalizedCompactHaar
        (E.system (L.subsequence n)).base.Gauge)‖

/-- Forget the explicit density and boundary coordinates while retaining the
finite-volume pullback positivity they generate. -/
noncomputable def
    PhysicalYangMillsOrientedWilsonOSBoundaryFiberedGibbsBochnerData.toPullbackCertificate
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E.PhysicalGaugeAction}
    {L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L)}
    (C : PhysicalYangMillsOrientedWilsonOSBoundaryFiberedGibbsBochnerData
      G L D) :
    PhysicalYangMillsOrientedWilsonOSPullbackCertificate G L D where
  finiteReflectionPositive n F :=
    physical_yang_mills_oriented_boundaryFiberedGibbsBochner_pullbackForm_nonneg
      G L D C n F

/-- The scale-dependent density-weighted boundary Gram package proves
reflection positivity of every approximating physical state. -/
theorem physical_yang_mills_oriented_boundaryFiberedGibbsBochner_approximating_reflectionPositive
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L))
    (C : PhysicalYangMillsOrientedWilsonOSBoundaryFiberedGibbsBochnerData
      G L D)
    (n : ℕ) :
    D.WeakStarReflectionPositive
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState
        (G.toSymmetryLimit L) n) :=
  physical_yang_mills_oriented_pullback_approximating_reflectionPositive
    G L D C.toPullbackCertificate n

/-- The same package transfers reflection positivity to the continuum
weak-star state. -/
theorem physical_yang_mills_oriented_boundaryFiberedGibbsBochner_continuum_reflectionPositive
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L))
    (C : PhysicalYangMillsOrientedWilsonOSBoundaryFiberedGibbsBochnerData
      G L D) :
    D.WeakStarReflectionPositive
      (physicalYangMillsContinuumGaugeInvariantWeakStarState
        (G.toSymmetryLimit L)) :=
  physical_yang_mills_oriented_pullback_continuum_reflectionPositive
    G L D C.toPullbackCertificate

end

end MathlibAnalytic
end MGAP4D
