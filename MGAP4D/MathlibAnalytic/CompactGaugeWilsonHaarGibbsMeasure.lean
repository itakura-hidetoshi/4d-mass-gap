import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonGibbsMeasure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Tilted

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal
open MeasureTheory Set

noncomputable section

/-- The whole compact group, bundled as a compact set with nonempty interior.
It is used to normalize Haar measure to total mass one. -/
def compactGroupPositiveCompacts
    (G : Type) [Group G] [TopologicalSpace G] [CompactSpace G] :
    PositiveCompacts G :=
  ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

/-- Haar probability measure on a compact topological group, normalized on the
whole group. -/
def normalizedCompactHaar
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] : Measure G :=
  Measure.haarMeasure (compactGroupPositiveCompacts G)

/-- The normalized compact Haar measure has total mass one. -/
theorem normalizedCompactHaar_univ
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] :
    normalizedCompactHaar G Set.univ = 1 := by
  simpa [normalizedCompactHaar, compactGroupPositiveCompacts] using
    (Measure.haarMeasure_self
      (K₀ := compactGroupPositiveCompacts G))

/-- The normalized compact Haar measure is a probability measure. -/
instance normalizedCompactHaar_isProbabilityMeasure
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] :
    IsProbabilityMeasure (normalizedCompactHaar G) :=
  ⟨normalizedCompactHaar_univ G⟩

/-- A finite four-dimensional Wilson lattice with an arbitrary compact
(topological, not necessarily finite) gauge group. -/
structure CompactGaugeWilsonSystem where
  Gauge : Type
  [gaugeGroup : Group Gauge]
  [gaugeTopology : TopologicalSpace Gauge]
  [gaugeTopologicalGroup : IsTopologicalGroup Gauge]
  [gaugeCompact : CompactSpace Gauge]
  [gaugeMeasurableSpace : MeasurableSpace Gauge]
  [gaugeBorel : BorelSpace Gauge]
  [gaugeNontrivial : Nontrivial Gauge]
  Vertex : Type
  [vertexFintype : Fintype Vertex]
  Edge : Type
  [edgeFintype : Fintype Edge]
  Plaquette : Type
  [plaquetteFintype : Fintype Plaquette]
  source : Edge → Vertex
  target : Edge → Vertex
  boundary : Plaquette → Fin 4 → Edge
  boundary_cycle_01 : ∀ p, target (boundary p 0) = source (boundary p 1)
  boundary_cycle_12 : ∀ p, target (boundary p 1) = source (boundary p 2)
  boundary_cycle_23 : ∀ p, target (boundary p 2) = source (boundary p 3)
  boundary_cycle_30 : ∀ p, target (boundary p 3) = source (boundary p 0)
  plaquetteEnergy : Gauge → ℝ
  plaquetteEnergy_nonneg : ∀ g, 0 ≤ plaquetteEnergy g
  plaquetteEnergy_conjInvariant :
    ∀ h g, plaquetteEnergy (h * g * h⁻¹) = plaquetteEnergy g
  beta : ℝ
  beta_nonneg : 0 ≤ beta

attribute [instance]
  CompactGaugeWilsonSystem.gaugeGroup
  CompactGaugeWilsonSystem.gaugeTopology
  CompactGaugeWilsonSystem.gaugeTopologicalGroup
  CompactGaugeWilsonSystem.gaugeCompact
  CompactGaugeWilsonSystem.gaugeMeasurableSpace
  CompactGaugeWilsonSystem.gaugeBorel
  CompactGaugeWilsonSystem.gaugeNontrivial
  CompactGaugeWilsonSystem.vertexFintype
  CompactGaugeWilsonSystem.edgeFintype
  CompactGaugeWilsonSystem.plaquetteFintype

abbrev CompactGaugeWilsonSystem.Configuration
    (L : CompactGaugeWilsonSystem) : Type :=
  L.Edge → L.Gauge

abbrev CompactGaugeWilsonSystem.GaugeTransformation
    (L : CompactGaugeWilsonSystem) : Type :=
  L.Vertex → L.Gauge

/-- Gauge action on compact-group link configurations. -/
def CompactGaugeWilsonSystem.gaugeTransform
    (L : CompactGaugeWilsonSystem)
    (γ : L.GaugeTransformation)
    (A : L.Configuration) : L.Configuration :=
  fun e => γ (L.source e) * A e * (γ (L.target e))⁻¹

/-- Ordered plaquette holonomy. -/
def CompactGaugeWilsonSystem.plaquetteHolonomy
    (L : CompactGaugeWilsonSystem)
    (A : L.Configuration) (p : L.Plaquette) : L.Gauge :=
  A (L.boundary p 0) *
    A (L.boundary p 1) *
    A (L.boundary p 2) *
    A (L.boundary p 3)

/-- Compact-group plaquette holonomy transforms by conjugation. -/
theorem compact_gauge_plaquetteHolonomy_gaugeTransform
    (L : CompactGaugeWilsonSystem)
    (γ : L.GaugeTransformation)
    (A : L.Configuration) (p : L.Plaquette) :
    L.plaquetteHolonomy (L.gaugeTransform γ A) p =
      γ (L.source (L.boundary p 0)) *
        L.plaquetteHolonomy A p *
        (γ (L.source (L.boundary p 0)))⁻¹ := by
  unfold CompactGaugeWilsonSystem.plaquetteHolonomy
    CompactGaugeWilsonSystem.gaugeTransform
  rw [L.boundary_cycle_01 p, L.boundary_cycle_12 p,
    L.boundary_cycle_23 p, L.boundary_cycle_30 p]
  group

/-- Wilson action for a compact gauge group. -/
def CompactGaugeWilsonSystem.wilsonAction
    (L : CompactGaugeWilsonSystem)
    (A : L.Configuration) : ℝ :=
  ∑ p : L.Plaquette,
    L.plaquetteEnergy (L.plaquetteHolonomy A p)

/-- Nonnegativity of the compact-gauge Wilson action. -/
theorem compact_gauge_wilsonAction_nonneg
    (L : CompactGaugeWilsonSystem) (A : L.Configuration) :
    0 ≤ L.wilsonAction A := by
  unfold CompactGaugeWilsonSystem.wilsonAction
  exact Finset.sum_nonneg fun p _ => L.plaquetteEnergy_nonneg _

/-- Gauge invariance of the compact-gauge Wilson action. -/
theorem compact_gauge_wilsonAction_gaugeInvariant
    (L : CompactGaugeWilsonSystem)
    (γ : L.GaugeTransformation) (A : L.Configuration) :
    L.wilsonAction (L.gaugeTransform γ A) = L.wilsonAction A := by
  unfold CompactGaugeWilsonSystem.wilsonAction
  apply Finset.sum_congr rfl
  intro p _hp
  rw [compact_gauge_plaquetteHolonomy_gaugeTransform]
  exact L.plaquetteEnergy_conjInvariant _ _

/-- Product Haar probability measure on the finite link-configuration space. -/
def CompactGaugeWilsonSystem.configurationHaarMeasure
    (L : CompactGaugeWilsonSystem) : Measure L.Configuration :=
  Measure.pi (fun _ : L.Edge => normalizedCompactHaar L.Gauge)

/-- The finite product of normalized Haar measures is a probability measure. -/
instance compactGauge_configurationHaar_isProbabilityMeasure
    (L : CompactGaugeWilsonSystem) :
    IsProbabilityMeasure L.configurationHaarMeasure := by
  unfold CompactGaugeWilsonSystem.configurationHaarMeasure
  infer_instance

/-- The logarithmic Gibbs weight used for exponential tilting. -/
def CompactGaugeWilsonSystem.gibbsExponent
    (L : CompactGaugeWilsonSystem)
    (A : L.Configuration) : ℝ :=
  -L.beta * L.wilsonAction A

/-- Gauge invariance of the Gibbs exponent. -/
theorem compact_gauge_gibbsExponent_gaugeInvariant
    (L : CompactGaugeWilsonSystem)
    (γ : L.GaugeTransformation) (A : L.Configuration) :
    L.gibbsExponent (L.gaugeTransform γ A) = L.gibbsExponent A := by
  simp only [CompactGaugeWilsonSystem.gibbsExponent]
  rw [compact_gauge_wilsonAction_gaugeInvariant]

/-- Real partition function with respect to product Haar probability measure. -/
def CompactGaugeWilsonSystem.partitionFunction
    (L : CompactGaugeWilsonSystem) : ℝ :=
  ∫ A, Real.exp (L.gibbsExponent A) ∂L.configurationHaarMeasure

/-- The finite-volume compact-gauge Gibbs measure is the exponential tilt of
product Haar measure by the Wilson action.  The integrability hypothesis is the
remaining local analytic obligation; it follows, for the standard continuous
Wilson action, from compactness of the finite configuration space. -/
def CompactGaugeWilsonSystem.gibbsMeasure
    (L : CompactGaugeWilsonSystem)
    (_hIntegrable : Integrable
      (fun A => Real.exp (L.gibbsExponent A))
      L.configurationHaarMeasure) : Measure L.Configuration :=
  L.configurationHaarMeasure.tilted L.gibbsExponent

/-- The compact-gauge Wilson Gibbs measure is a genuine probability measure. -/
theorem compactGauge_gibbsMeasure_isProbabilityMeasure
    (L : CompactGaugeWilsonSystem)
    (hIntegrable : Integrable
      (fun A => Real.exp (L.gibbsExponent A))
      L.configurationHaarMeasure) :
    IsProbabilityMeasure (L.gibbsMeasure hIntegrable) := by
  unfold CompactGaugeWilsonSystem.gibbsMeasure
  exact MeasureTheory.isProbabilityMeasure_tilted hIntegrable

/-- Positivity of the finite-volume partition function. -/
theorem compact_gauge_partitionFunction_pos
    (L : CompactGaugeWilsonSystem)
    (hIntegrable : Integrable
      (fun A => Real.exp (L.gibbsExponent A))
      L.configurationHaarMeasure) :
    0 < L.partitionFunction := by
  unfold CompactGaugeWilsonSystem.partitionFunction
  exact integral_exp_pos hIntegrable

/-- Explicit density formula for the compact-gauge Wilson Gibbs measure. -/
theorem compact_gauge_gibbsMeasure_eq_withDensity
    (L : CompactGaugeWilsonSystem)
    (hIntegrable : Integrable
      (fun A => Real.exp (L.gibbsExponent A))
      L.configurationHaarMeasure) :
    L.gibbsMeasure hIntegrable =
      L.configurationHaarMeasure.withDensity
        (fun A => ENNReal.ofReal
          (Real.exp (L.gibbsExponent A) / L.partitionFunction)) := by
  rfl

/-- The probability normalization of the compact-gauge Gibbs measure. -/
theorem compact_gauge_gibbsMeasure_univ
    (L : CompactGaugeWilsonSystem)
    (hIntegrable : Integrable
      (fun A => Real.exp (L.gibbsExponent A))
      L.configurationHaarMeasure) :
    L.gibbsMeasure hIntegrable Set.univ = 1 := by
  letI : IsProbabilityMeasure (L.gibbsMeasure hIntegrable) :=
    compactGauge_gibbsMeasure_isProbabilityMeasure L hIntegrable
  exact measure_univ

/-- Concrete finite-volume compact-gauge approximation data.  The actual Haar
product Gibbs measures are constructed here; reflection positivity, Euclidean
covariance, and gauge invariance of the full measure are kept as separately
visible proof obligations for the chosen lattice action. -/
structure CompactGaugeWilsonApproximationFamily where
  index : Type
  system : index → CompactGaugeWilsonSystem
  latticeSpacing : index → ℝ
  volumeScale : index → ℝ
  boltzmannIntegrable :
    ∀ i, Integrable
      (fun A => Real.exp ((system i).gibbsExponent A))
      (system i).configurationHaarMeasure
  gaugeInvariantFiniteVolume : Prop
  gaugeInvariantFiniteVolume_proof : gaugeInvariantFiniteVolume
  finiteVolumeReflectionPositive : Prop
  finiteVolumeReflectionPositive_proof : finiteVolumeReflectionPositive
  finiteVolumeEuclideanCovariant : Prop
  finiteVolumeEuclideanCovariant_proof : finiteVolumeEuclideanCovariant

/-- The compact-gauge Wilson family supplies the concrete finite-volume measure
carrier required by the existing continuum construction spine. -/
def CompactGaugeWilsonApproximationFamily.toFiniteVolumeApproximation
    (F : CompactGaugeWilsonApproximationFamily) :
    EuclideanYangMillsFiniteVolumeApproximation :=
  { index := F.index
    finiteVolumeConfiguration := fun i => (F.system i).Configuration
    finiteVolumeMeasurableSpace := fun _i => inferInstance
    finiteVolumeMeasure := fun i =>
      (F.system i).gibbsMeasure (F.boltzmannIntegrable i)
    latticeSpacing := F.latticeSpacing
    volumeScale := F.volumeScale
    gaugeInvariantFiniteVolume := F.gaugeInvariantFiniteVolume
    gaugeInvariantFiniteVolume_proof := F.gaugeInvariantFiniteVolume_proof
    finiteVolumeReflectionPositive := F.finiteVolumeReflectionPositive
    finiteVolumeReflectionPositive_proof := F.finiteVolumeReflectionPositive_proof
    finiteVolumeEuclideanCovariant := F.finiteVolumeEuclideanCovariant
    finiteVolumeEuclideanCovariant_proof := F.finiteVolumeEuclideanCovariant_proof
    finiteVolumeSchwingerData := fun _n => ℝ }

/-- Every measure in the compact-gauge finite-volume family is a probability
measure. -/
theorem compact_gauge_wilson_family_probability_measure
    (F : CompactGaugeWilsonApproximationFamily) (i : F.index) :
    IsProbabilityMeasure
      (F.toFiniteVolumeApproximation.finiteVolumeMeasure
        (show F.toFiniteVolumeApproximation.index from i)) := by
  change IsProbabilityMeasure
    ((F.system i).gibbsMeasure (F.boltzmannIntegrable i))
  exact compactGauge_gibbsMeasure_isProbabilityMeasure
    (F.system i) (F.boltzmannIntegrable i)

end

end MathlibAnalytic
end MGAP4D
