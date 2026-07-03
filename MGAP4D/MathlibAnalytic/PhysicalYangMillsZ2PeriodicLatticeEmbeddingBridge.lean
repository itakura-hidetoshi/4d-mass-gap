import MGAP4D.MathlibAnalytic.PhysicalYangMillsLatticeEmbedding
import MGAP4D.MathlibAnalytic.PhysicalYangMillsZ2PeriodicPlaquetteInterpolationBridge
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Function

noncomputable section

local instance (k : ℕ) :
    NeZero (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k) :=
  ⟨by
    unfold z2PeriodicHypercubicOrientedPlaquetteLimitVolume
    omega⟩

/-- Model-dependent realization of the periodic finite-volume `Z₂` Wilson system
inside the lattice configuration sequence of a generic physical lattice
embedding.

The realization map is required to transport the actual finite `Z₂` Gibbs
measure to the lattice measure stored by the embedding.  The physical
interpolation map, its measurability, and its scaling data remain those already
carried by `E`. -/
structure PhysicalYangMillsZ2PeriodicLatticeEmbeddingBridge
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding)
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ) where
  realize :
    ∀ k : ℕ,
      (z2PeriodicHypercubicOrientedWilsonSystem
        (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
        beta hBeta.le).Configuration →
      E.LatticeConfiguration k
  realize_measurePreserving :
    ∀ k : ℕ,
      MeasurePreserving (realize k)
        (z2PeriodicHypercubicOrientedWilsonSystem
          (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
          beta hBeta.le).gibbsMeasure
        (E.latticeMeasure k : Measure (E.LatticeConfiguration k))
  sourceObservable :
    BoundedContinuousFunction E.PhysicalConfiguration ℝ
  targetObservable :
    BoundedContinuousFunction E.PhysicalConfiguration ℝ
  sourcePlaquette :
    ∀ k : ℕ,
      PeriodicHypercubicPlaquette
        (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
  targetPlaquette :
    ∀ k : ℕ,
      PeriodicHypercubicPlaquette
        (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
  distance_eq :
    ∀ k : ℕ,
      periodicHypercubicPlaquetteBaseL1Distance
          (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
          (sourcePlaquette k)
          (targetPlaquette k) =
        distance
  source_pullback :
    ∀ (k : ℕ)
      (U :
        (z2PeriodicHypercubicOrientedWilsonSystem
          (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
          beta hBeta.le).Configuration),
      sourceObservable (E.interpolate k (realize k U)) =
        FiniteOrientedLatticeWilsonSystem.plaquetteObservable
          (z2PeriodicHypercubicOrientedWilsonSystem
            (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
            beta hBeta.le)
          (sourcePlaquette k) U
  target_pullback :
    ∀ (k : ℕ)
      (U :
        (z2PeriodicHypercubicOrientedWilsonSystem
          (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
          beta hBeta.le).Configuration),
      targetObservable (E.interpolate k (realize k U)) =
        FiniteOrientedLatticeWilsonSystem.plaquetteObservable
          (z2PeriodicHypercubicOrientedWilsonSystem
            (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
            beta hBeta.le)
          (targetPlaquette k) U

/-- The embedded approximation is the pushforward of the periodic `Z₂` Gibbs
measure through the composite of the realization and physical interpolation
maps. -/
theorem
    PhysicalYangMillsZ2PeriodicLatticeEmbeddingBridge.embeddedMeasure_toMeasure_eq_composite_map
    {E : PhysicalFourDimensionalYangMillsLatticeEmbedding}
    {beta : ℝ}
    {hBeta : 0 < beta}
    {distance : ℕ}
    (B :
      PhysicalYangMillsZ2PeriodicLatticeEmbeddingBridge
        E beta hBeta distance)
    (k : ℕ) :
    ProbabilityMeasure.toMeasure (E.embeddedMeasure k) =
      Measure.map (fun U => E.interpolate k (B.realize k U))
        (z2PeriodicHypercubicOrientedWilsonSystem
          (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
          beta hBeta.le).gibbsMeasure := by
  change
    Measure.map (E.interpolate k)
        (E.latticeMeasure k : Measure (E.LatticeConfiguration k)) =
      Measure.map (fun U => E.interpolate k (B.realize k U))
        (z2PeriodicHypercubicOrientedWilsonSystem
          (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
          beta hBeta.le).gibbsMeasure
  calc
    Measure.map (E.interpolate k)
        (E.latticeMeasure k : Measure (E.LatticeConfiguration k)) =
      Measure.map (E.interpolate k)
        (Measure.map (B.realize k)
          (z2PeriodicHypercubicOrientedWilsonSystem
            (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
            beta hBeta.le).gibbsMeasure) := by
      rw [← (B.realize_measurePreserving k).map_eq]
    _ =
      Measure.map (E.interpolate k ∘ B.realize k)
        (z2PeriodicHypercubicOrientedWilsonSystem
          (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
          beta hBeta.le).gibbsMeasure :=
      Measure.map_map (E.interpolate_measurable k)
        (B.realize_measurePreserving k).measurable
    _ =
      Measure.map (fun U => E.interpolate k (B.realize k U))
        (z2PeriodicHypercubicOrientedWilsonSystem
          (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
          beta hBeta.le).gibbsMeasure := by
      rfl

/-- A periodic `Z₂` realization inside a generic lattice embedding automatically
produces the interpolation bridge of the preceding layer after a weak limit of
the embedded measures has been supplied. -/
noncomputable def
    PhysicalYangMillsZ2PeriodicLatticeEmbeddingBridge.toInterpolationBridge
    {E : PhysicalFourDimensionalYangMillsLatticeEmbedding}
    {beta : ℝ}
    {hBeta : 0 < beta}
    {distance : ℕ}
    (B :
      PhysicalYangMillsZ2PeriodicLatticeEmbeddingBridge
        E beta hBeta distance)
    (continuumMeasure : ProbabilityMeasure E.PhysicalConfiguration)
    (hWeak :
      Tendsto E.embeddedMeasure atTop (nhds continuumMeasure)) :
    PhysicalYangMillsZ2PeriodicPlaquetteInterpolationBridge
      (E.toWeakLimit continuumMeasure hWeak)
      beta hBeta distance :=
  { interpolate := fun k U => E.interpolate k (B.realize k U)
    interpolate_measurable := fun k =>
      (E.interpolate_measurable k).comp
        (B.realize_measurePreserving k).measurable
    approximatingMeasure_eq_map := fun k => by
      change ProbabilityMeasure.toMeasure (E.embeddedMeasure k) = _
      exact B.embeddedMeasure_toMeasure_eq_composite_map k
    sourceObservable := B.sourceObservable
    targetObservable := B.targetObservable
    sourcePlaquette := B.sourcePlaquette
    targetPlaquette := B.targetPlaquette
    distance_eq := B.distance_eq
    source_pullback := B.source_pullback
    target_pullback := B.target_pullback }

/-- The composite interpolation bridge identifies the actual finite plaquette
covariance with the connected correlation of the embedded approximation. -/
theorem
    PhysicalYangMillsZ2PeriodicLatticeEmbeddingBridge.finiteCovariance_eq
    {E : PhysicalFourDimensionalYangMillsLatticeEmbedding}
    {beta : ℝ}
    {hBeta : 0 < beta}
    {distance : ℕ}
    (B :
      PhysicalYangMillsZ2PeriodicLatticeEmbeddingBridge
        E beta hBeta distance)
    (continuumMeasure : ProbabilityMeasure E.PhysicalConfiguration)
    (hWeak :
      Tendsto E.embeddedMeasure atTop (nhds continuumMeasure))
    (k : ℕ) :
    FiniteOrientedLatticeWilsonSystem.gibbsCovarianceReal
        (z2PeriodicHypercubicOrientedWilsonSystem
          (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
          beta hBeta.le)
        (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
          (z2PeriodicHypercubicOrientedWilsonSystem
            (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
            beta hBeta.le)
          (B.sourcePlaquette k))
        (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
          (z2PeriodicHypercubicOrientedWilsonSystem
            (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
            beta hBeta.le)
          (B.targetPlaquette k)) =
      (E.toWeakLimit continuumMeasure hWeak).approximatingConnectedCorrelation
        k B.sourceObservable B.targetObservable :=
  (B.toInterpolationBridge continuumMeasure hWeak).finiteCovariance_eq k

/-- The lattice-embedding realization automatically supplies the weak-limit
covariance bridge used to pass uniform finite-volume clustering to the continuum
connected correlation. -/
noncomputable def
    PhysicalYangMillsZ2PeriodicLatticeEmbeddingBridge.toWeakLimitBridge
    {E : PhysicalFourDimensionalYangMillsLatticeEmbedding}
    {beta : ℝ}
    {hBeta : 0 < beta}
    {distance : ℕ}
    (B :
      PhysicalYangMillsZ2PeriodicLatticeEmbeddingBridge
        E beta hBeta distance)
    (continuumMeasure : ProbabilityMeasure E.PhysicalConfiguration)
    (hWeak :
      Tendsto E.embeddedMeasure atTop (nhds continuumMeasure)) :
    PhysicalYangMillsZ2PeriodicPlaquetteCovarianceWeakLimitBridge
      (E.toWeakLimit continuumMeasure hWeak)
      beta hBeta distance :=
  (B.toInterpolationBridge continuumMeasure hWeak).toWeakLimitBridge

/-- Once the periodic `Z₂` realization and weak convergence of the embedded laws
are available, the volume-uniform finite plaquette clustering estimate passes to
the continuum connected correlation. -/
theorem
    PhysicalYangMillsZ2PeriodicLatticeEmbeddingBridge.continuumConnectedCorrelation_abs_le
    {E : PhysicalFourDimensionalYangMillsLatticeEmbedding}
    {beta : ℝ}
    {hBeta : 0 < beta}
    {distance : ℕ}
    (K :
      Z2PeriodicHypercubicOrientedPlaquetteUniformSpatialClusteringFamilyCertificate
        beta hBeta)
    (B :
      PhysicalYangMillsZ2PeriodicLatticeEmbeddingBridge
        E beta hBeta distance)
    (continuumMeasure : ProbabilityMeasure E.PhysicalConfiguration)
    (hWeak :
      Tendsto E.embeddedMeasure atTop (nhds continuumMeasure)) :
    |(E.toWeakLimit continuumMeasure hWeak).continuumConnectedCorrelation
        B.sourceObservable B.targetObservable| ≤
      z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta *
        Real.exp
          (-z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta *
            (distance : ℝ)) :=
  (B.toInterpolationBridge continuumMeasure hWeak)
    .continuumConnectedCorrelation_abs_le K

end

end MathlibAnalytic
end MGAP4D
