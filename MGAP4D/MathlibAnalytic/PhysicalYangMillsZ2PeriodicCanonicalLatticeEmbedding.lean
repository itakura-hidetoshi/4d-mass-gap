import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonGibbsMeasure
import MGAP4D.MathlibAnalytic.PhysicalYangMillsZ2PeriodicLatticeEmbeddingBridge
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

local instance (k : ℕ) :
    NeZero (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k) :=
  ⟨by
    unfold z2PeriodicHypercubicOrientedPlaquetteLimitVolume
    omega⟩

/-- The normalized Gibbs law of any finite orientation-correct Wilson system,
bundled as a Mathlib probability measure. -/
noncomputable def
    FiniteOrientedLatticeWilsonSystem.gibbsProbabilityMeasure
    (L : FiniteOrientedLatticeWilsonSystem) :
    ProbabilityMeasure L.Configuration :=
  ⟨L.gibbsMeasure,
    finiteOrientedLatticeWilsonSystem_gibbsMeasure_isProbabilityMeasure L⟩

@[simp]
theorem
    finite_oriented_gibbsProbabilityMeasure_toMeasure
    (L : FiniteOrientedLatticeWilsonSystem) :
    (L.gibbsProbabilityMeasure : Measure L.Configuration) =
      L.gibbsMeasure :=
  rfl

/-- The identity map transports a finite oriented Gibbs measure to its bundled
probability-measure carrier. -/
theorem
    finite_oriented_gibbsProbabilityMeasure_id_measurePreserving
    (L : FiniteOrientedLatticeWilsonSystem) :
    MeasurePreserving (id : L.Configuration → L.Configuration)
      L.gibbsMeasure
      (L.gibbsProbabilityMeasure : Measure L.Configuration) := by
  simpa using (MeasurePreserving.id L.gibbsMeasure)

/-- Canonical finite-lattice packaging of the periodic four-dimensional `Z₂`
Wilson systems inside one physical lattice-embedding sequence.

The lattice configuration at index `k` is definitionally the configuration
space of the periodic system of side length `k + 3`, and the lattice law is its
actual normalized Gibbs probability measure.  The common physical carrier,
interpolation maps, and physical scaling data remain model-dependent inputs.
Thus this structure packages the finite laws canonically without asserting weak
convergence or constructing an infinite-volume state. -/
structure
    PhysicalYangMillsZ2PeriodicCanonicalLatticeEmbedding
    (beta : ℝ)
    (hBeta : 0 < beta) where
  PhysicalConfiguration : Type
  [physicalTopologicalSpace : TopologicalSpace PhysicalConfiguration]
  [physicalMeasurableSpace : MeasurableSpace PhysicalConfiguration]
  [physicalBorelSpace : BorelSpace PhysicalConfiguration]
  [physicalPolishSpace : PolishSpace PhysicalConfiguration]
  interpolate :
    ∀ k : ℕ,
      (z2PeriodicHypercubicOrientedWilsonSystem
        (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
        beta hBeta.le).Configuration →
      PhysicalConfiguration
  interpolate_measurable : ∀ k : ℕ, Measurable (interpolate k)
  latticeSpacing : ℕ → ℝ
  latticeSpacing_pos : ∀ k : ℕ, 0 < latticeSpacing k
  latticeSpacing_tendsto_zero :
    Tendsto latticeSpacing atTop (nhds 0)
  physicalVolume : ℕ → ℝ
  physicalVolume_tendsto_atTop :
    Tendsto physicalVolume atTop atTop

attribute [instance]
  PhysicalYangMillsZ2PeriodicCanonicalLatticeEmbedding.physicalTopologicalSpace
  PhysicalYangMillsZ2PeriodicCanonicalLatticeEmbedding.physicalMeasurableSpace
  PhysicalYangMillsZ2PeriodicCanonicalLatticeEmbedding.physicalBorelSpace
  PhysicalYangMillsZ2PeriodicCanonicalLatticeEmbedding.physicalPolishSpace

/-- Forget the canonical periodic `Z₂` origin while retaining the actual finite
Gibbs laws, the supplied interpolation maps, and the physical scaling data. -/
noncomputable def
    PhysicalYangMillsZ2PeriodicCanonicalLatticeEmbedding.toLatticeEmbedding
    {beta : ℝ}
    {hBeta : 0 < beta}
    (E : PhysicalYangMillsZ2PeriodicCanonicalLatticeEmbedding beta hBeta) :
    PhysicalFourDimensionalYangMillsLatticeEmbedding :=
  { PhysicalConfiguration := E.PhysicalConfiguration
    LatticeConfiguration := fun k =>
      (z2PeriodicHypercubicOrientedWilsonSystem
        (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
        beta hBeta.le).Configuration
    latticeMeasure := fun k =>
      (z2PeriodicHypercubicOrientedWilsonSystem
        (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
        beta hBeta.le).gibbsProbabilityMeasure
    interpolate := E.interpolate
    interpolate_measurable := E.interpolate_measurable
    latticeSpacing := E.latticeSpacing
    latticeSpacing_pos := E.latticeSpacing_pos
    latticeSpacing_tendsto_zero := E.latticeSpacing_tendsto_zero
    physicalVolume := E.physicalVolume
    physicalVolume_tendsto_atTop := E.physicalVolume_tendsto_atTop }

/-- The lattice configuration type of the canonical embedding is exactly the
periodic finite-volume `Z₂` configuration type. -/
theorem
    PhysicalYangMillsZ2PeriodicCanonicalLatticeEmbedding.latticeConfiguration_eq
    {beta : ℝ}
    {hBeta : 0 < beta}
    (E : PhysicalYangMillsZ2PeriodicCanonicalLatticeEmbedding beta hBeta)
    (k : ℕ) :
    E.toLatticeEmbedding.LatticeConfiguration k =
      (z2PeriodicHypercubicOrientedWilsonSystem
        (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
        beta hBeta.le).Configuration :=
  rfl

/-- The measure stored by the canonical lattice embedding is definitionally the
normalized periodic finite-volume Gibbs probability measure. -/
theorem
    PhysicalYangMillsZ2PeriodicCanonicalLatticeEmbedding.latticeMeasure_eq
    {beta : ℝ}
    {hBeta : 0 < beta}
    (E : PhysicalYangMillsZ2PeriodicCanonicalLatticeEmbedding beta hBeta)
    (k : ℕ) :
    E.toLatticeEmbedding.latticeMeasure k =
      (z2PeriodicHypercubicOrientedWilsonSystem
        (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
        beta hBeta.le).gibbsProbabilityMeasure :=
  rfl

/-- After coercion to ordinary measures, the canonical lattice law is the
previously constructed finite periodic Gibbs measure. -/
@[simp]
theorem
    PhysicalYangMillsZ2PeriodicCanonicalLatticeEmbedding.latticeMeasure_toMeasure
    {beta : ℝ}
    {hBeta : 0 < beta}
    (E : PhysicalYangMillsZ2PeriodicCanonicalLatticeEmbedding beta hBeta)
    (k : ℕ) :
    (E.toLatticeEmbedding.latticeMeasure k :
        Measure (E.toLatticeEmbedding.LatticeConfiguration k)) =
      (z2PeriodicHypercubicOrientedWilsonSystem
        (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
        beta hBeta.le).gibbsMeasure :=
  rfl

/-- The embedded approximation is exactly the pushforward of the periodic
finite-volume Gibbs probability measure by the supplied interpolation map. -/
theorem
    PhysicalYangMillsZ2PeriodicCanonicalLatticeEmbedding.embeddedMeasure_eq
    {beta : ℝ}
    {hBeta : 0 < beta}
    (E : PhysicalYangMillsZ2PeriodicCanonicalLatticeEmbedding beta hBeta)
    (k : ℕ) :
    E.toLatticeEmbedding.embeddedMeasure k =
      (z2PeriodicHypercubicOrientedWilsonSystem
        (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
        beta hBeta.le).gibbsProbabilityMeasure.map
          (E.interpolate_measurable k).aemeasurable :=
  rfl

/-- The canonical realization of a periodic finite-volume configuration inside
its own lattice configuration type is the identity map. -/
def
    PhysicalYangMillsZ2PeriodicCanonicalLatticeEmbedding.realize
    {beta : ℝ}
    {hBeta : 0 < beta}
    (E : PhysicalYangMillsZ2PeriodicCanonicalLatticeEmbedding beta hBeta)
    (k : ℕ) :
    (z2PeriodicHypercubicOrientedWilsonSystem
      (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
      beta hBeta.le).Configuration →
      E.toLatticeEmbedding.LatticeConfiguration k :=
  id

@[simp]
theorem
    PhysicalYangMillsZ2PeriodicCanonicalLatticeEmbedding.realize_apply
    {beta : ℝ}
    {hBeta : 0 < beta}
    (E : PhysicalYangMillsZ2PeriodicCanonicalLatticeEmbedding beta hBeta)
    (k : ℕ)
    (U :
      (z2PeriodicHypercubicOrientedWilsonSystem
        (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
        beta hBeta.le).Configuration) :
    E.realize k U = U :=
  rfl

/-- The canonical identity realization preserves the actual finite periodic
Gibbs law.  Hence no independent realization or pushforward hypothesis remains
at this layer. -/
theorem
    PhysicalYangMillsZ2PeriodicCanonicalLatticeEmbedding.realize_measurePreserving
    {beta : ℝ}
    {hBeta : 0 < beta}
    (E : PhysicalYangMillsZ2PeriodicCanonicalLatticeEmbedding beta hBeta)
    (k : ℕ) :
    MeasurePreserving (E.realize k)
      (z2PeriodicHypercubicOrientedWilsonSystem
        (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
        beta hBeta.le).gibbsMeasure
      (E.toLatticeEmbedding.latticeMeasure k :
        Measure (E.toLatticeEmbedding.LatticeConfiguration k)) := by
  exact finite_oriented_gibbsProbabilityMeasure_id_measurePreserving
    (z2PeriodicHypercubicOrientedWilsonSystem
      (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
      beta hBeta.le)

/-- Model-dependent local-observable data on top of the canonical finite `Z₂`
lattice packaging.

Only the common-space observables, their plaquette pullbacks, and the fixed
geometric separation remain as inputs.  The finite configuration sequence,
finite Gibbs laws, realization map, and realization measure preservation are
already fixed by `E`. -/
structure
    PhysicalYangMillsZ2PeriodicCanonicalPlaquetteData
    {beta : ℝ}
    {hBeta : 0 < beta}
    (E : PhysicalYangMillsZ2PeriodicCanonicalLatticeEmbedding beta hBeta)
    (distance : ℕ) where
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
      sourceObservable (E.interpolate k U) =
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
      targetObservable (E.interpolate k U) =
        FiniteOrientedLatticeWilsonSystem.plaquetteObservable
          (z2PeriodicHypercubicOrientedWilsonSystem
            (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
            beta hBeta.le)
          (targetPlaquette k) U

/-- Canonical finite `Z₂` packaging turns local plaquette data directly into the
generic lattice-embedding bridge, using identity realization and its proved
measure preservation. -/
noncomputable def
    PhysicalYangMillsZ2PeriodicCanonicalPlaquetteData.toLatticeEmbeddingBridge
    {beta : ℝ}
    {hBeta : 0 < beta}
    {E : PhysicalYangMillsZ2PeriodicCanonicalLatticeEmbedding beta hBeta}
    {distance : ℕ}
    (D : PhysicalYangMillsZ2PeriodicCanonicalPlaquetteData E distance) :
    PhysicalYangMillsZ2PeriodicLatticeEmbeddingBridge
      E.toLatticeEmbedding beta hBeta distance :=
  { realize := E.realize
    realize_measurePreserving := E.realize_measurePreserving
    sourceObservable := D.sourceObservable
    targetObservable := D.targetObservable
    sourcePlaquette := D.sourcePlaquette
    targetPlaquette := D.targetPlaquette
    distance_eq := D.distance_eq
    source_pullback := fun k U => by
      simpa using D.source_pullback k U
    target_pullback := fun k U => by
      simpa using D.target_pullback k U }

/-- For canonical periodic `Z₂` finite-lattice data, weak convergence of the
interpolated laws is the only remaining measure-limit hypothesis needed to pass
the uniform finite-volume plaquette clustering estimate to the continuum
connected correlation. -/
theorem
    PhysicalYangMillsZ2PeriodicCanonicalPlaquetteData.continuumConnectedCorrelation_abs_le
    {beta : ℝ}
    {hBeta : 0 < beta}
    {E : PhysicalYangMillsZ2PeriodicCanonicalLatticeEmbedding beta hBeta}
    {distance : ℕ}
    (D : PhysicalYangMillsZ2PeriodicCanonicalPlaquetteData E distance)
    (K :
      Z2PeriodicHypercubicOrientedPlaquetteUniformSpatialClusteringFamilyCertificate
        beta hBeta)
    (continuumMeasure : ProbabilityMeasure E.PhysicalConfiguration)
    (hWeak :
      Tendsto E.toLatticeEmbedding.embeddedMeasure atTop
        (nhds continuumMeasure)) :
    |(E.toLatticeEmbedding.toWeakLimit continuumMeasure hWeak)
        .continuumConnectedCorrelation
          D.sourceObservable D.targetObservable| ≤
      z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta *
        Real.exp
          (-z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta *
            (distance : ℝ)) :=
  D.toLatticeEmbeddingBridge.continuumConnectedCorrelation_abs_le
    K continuumMeasure hWeak

end

end MathlibAnalytic
end MGAP4D
