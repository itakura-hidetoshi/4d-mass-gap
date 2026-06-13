import MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureConstructionSpine
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.SpecialFunctions.Exp

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal
open MeasureTheory

noncomputable section

/-- A finite oriented four-dimensional plaquette system with a finite gauge group.

The boundary of each plaquette is an ordered cycle of four directed edges.  This
is enough to define plaquette holonomy without imposing commutativity on the
gauge group. -/
structure FiniteLatticeWilsonSystem where
  Gauge : Type
  [gaugeGroup : Group Gauge]
  [gaugeFintype : Fintype Gauge]
  [gaugeInhabited : Inhabited Gauge]
  [gaugeNontrivial : Nontrivial Gauge]
  [gaugeMeasurableSpace : MeasurableSpace Gauge]
  [gaugeMeasurableSingleton : MeasurableSingletonClass Gauge]
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
  FiniteLatticeWilsonSystem.gaugeGroup
  FiniteLatticeWilsonSystem.gaugeFintype
  FiniteLatticeWilsonSystem.gaugeInhabited
  FiniteLatticeWilsonSystem.gaugeNontrivial
  FiniteLatticeWilsonSystem.gaugeMeasurableSpace
  FiniteLatticeWilsonSystem.gaugeMeasurableSingleton
  FiniteLatticeWilsonSystem.vertexFintype
  FiniteLatticeWilsonSystem.edgeFintype
  FiniteLatticeWilsonSystem.plaquetteFintype

/-- Link configurations on a finite lattice. -/
abbrev FiniteLatticeWilsonSystem.Configuration
    (L : FiniteLatticeWilsonSystem) : Type :=
  L.Edge → L.Gauge

/-- Finite-lattice gauge transformations. -/
abbrev FiniteLatticeWilsonSystem.GaugeTransformation
    (L : FiniteLatticeWilsonSystem) : Type :=
  L.Vertex → L.Gauge

/-- The usual left-right action of a gauge transformation on a link variable. -/
def FiniteLatticeWilsonSystem.gaugeTransform
    (L : FiniteLatticeWilsonSystem)
    (γ : L.GaugeTransformation)
    (A : L.Configuration) : L.Configuration :=
  fun e => γ (L.source e) * A e * (γ (L.target e))⁻¹

/-- Ordered plaquette holonomy around the four-edge boundary. -/
def FiniteLatticeWilsonSystem.plaquetteHolonomy
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration) (p : L.Plaquette) : L.Gauge :=
  A (L.boundary p 0) *
    A (L.boundary p 1) *
    A (L.boundary p 2) *
    A (L.boundary p 3)

/-- Plaquette holonomy transforms by conjugation at the initial vertex. -/
theorem finite_lattice_plaquetteHolonomy_gaugeTransform
    (L : FiniteLatticeWilsonSystem)
    (γ : L.GaugeTransformation)
    (A : L.Configuration) (p : L.Plaquette) :
    L.plaquetteHolonomy (L.gaugeTransform γ A) p =
      γ (L.source (L.boundary p 0)) *
        L.plaquetteHolonomy A p *
        (γ (L.source (L.boundary p 0)))⁻¹ := by
  unfold FiniteLatticeWilsonSystem.plaquetteHolonomy
    FiniteLatticeWilsonSystem.gaugeTransform
  rw [L.boundary_cycle_01 p, L.boundary_cycle_12 p,
    L.boundary_cycle_23 p, L.boundary_cycle_30 p]
  group

/-- Wilson plaquette action on a finite lattice. -/
def FiniteLatticeWilsonSystem.wilsonAction
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration) : ℝ :=
  ∑ p : L.Plaquette, L.plaquetteEnergy (L.plaquetteHolonomy A p)

/-- The finite Wilson action is nonnegative. -/
theorem finite_lattice_wilsonAction_nonneg
    (L : FiniteLatticeWilsonSystem) (A : L.Configuration) :
    0 ≤ L.wilsonAction A := by
  unfold FiniteLatticeWilsonSystem.wilsonAction
  exact Finset.sum_nonneg fun p _ => L.plaquetteEnergy_nonneg _

/-- Gauge invariance of the finite Wilson action. -/
theorem finite_lattice_wilsonAction_gaugeInvariant
    (L : FiniteLatticeWilsonSystem)
    (γ : L.GaugeTransformation) (A : L.Configuration) :
    L.wilsonAction (L.gaugeTransform γ A) = L.wilsonAction A := by
  unfold FiniteLatticeWilsonSystem.wilsonAction
  apply Finset.sum_congr rfl
  intro p _hp
  rw [finite_lattice_plaquetteHolonomy_gaugeTransform]
  exact L.plaquetteEnergy_conjInvariant _ _

/-- Unnormalized Boltzmann weight `exp (-β S(A))`, embedded in `ℝ≥0∞`. -/
def FiniteLatticeWilsonSystem.boltzmannWeight
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-L.beta * L.wilsonAction A))

/-- Every finite-lattice Boltzmann weight is strictly positive. -/
theorem finite_lattice_boltzmannWeight_pos
    (L : FiniteLatticeWilsonSystem) (A : L.Configuration) :
    0 < L.boltzmannWeight A := by
  rw [FiniteLatticeWilsonSystem.boltzmannWeight, ENNReal.ofReal_pos]
  exact Real.exp_pos _

/-- Every finite-lattice Boltzmann weight is nonzero. -/
theorem finite_lattice_boltzmannWeight_ne_zero
    (L : FiniteLatticeWilsonSystem) (A : L.Configuration) :
    L.boltzmannWeight A ≠ 0 :=
  ne_of_gt (finite_lattice_boltzmannWeight_pos L A)

/-- Boltzmann weights are gauge invariant. -/
theorem finite_lattice_boltzmannWeight_gaugeInvariant
    (L : FiniteLatticeWilsonSystem)
    (γ : L.GaugeTransformation) (A : L.Configuration) :
    L.boltzmannWeight (L.gaugeTransform γ A) = L.boltzmannWeight A := by
  simp only [FiniteLatticeWilsonSystem.boltzmannWeight]
  rw [finite_lattice_wilsonAction_gaugeInvariant]

/-- The finite partition function as an extended nonnegative real sum. -/
def FiniteLatticeWilsonSystem.partitionFunction
    (L : FiniteLatticeWilsonSystem) : ℝ≥0∞ :=
  ∑' A : L.Configuration, L.boltzmannWeight A

/-- The finite partition function is nonzero. -/
theorem finite_lattice_partitionFunction_ne_zero
    (L : FiniteLatticeWilsonSystem) :
    L.partitionFunction ≠ 0 := by
  intro hZero
  have hAll : ∀ A : L.Configuration, L.boltzmannWeight A = 0 :=
    ENNReal.tsum_eq_zero.mp hZero
  exact finite_lattice_boltzmannWeight_ne_zero L default (hAll default)

/-- The finite partition function is finite. -/
theorem finite_lattice_partitionFunction_ne_top
    (L : FiniteLatticeWilsonSystem) :
    L.partitionFunction ≠ ∞ := by
  unfold FiniteLatticeWilsonSystem.partitionFunction
  rw [tsum_fintype]
  exact ENNReal.sum_ne_top.2 fun A _hA => by
    simp [FiniteLatticeWilsonSystem.boltzmannWeight]

/-- The normalized finite-lattice Wilson Gibbs probability mass function. -/
def FiniteLatticeWilsonSystem.gibbsPMF
    (L : FiniteLatticeWilsonSystem) : PMF L.Configuration :=
  PMF.normalize L.boltzmannWeight
    (finite_lattice_partitionFunction_ne_zero L)
    (finite_lattice_partitionFunction_ne_top L)

/-- Pointwise Gibbs formula. -/
theorem finite_lattice_gibbsPMF_apply
    (L : FiniteLatticeWilsonSystem) (A : L.Configuration) :
    L.gibbsPMF A =
      L.boltzmannWeight A * L.partitionFunction⁻¹ := by
  rfl

/-- The Gibbs probability mass function is gauge invariant. -/
theorem finite_lattice_gibbsPMF_gaugeInvariant
    (L : FiniteLatticeWilsonSystem)
    (γ : L.GaugeTransformation) (A : L.Configuration) :
    L.gibbsPMF (L.gaugeTransform γ A) = L.gibbsPMF A := by
  rw [finite_lattice_gibbsPMF_apply, finite_lattice_gibbsPMF_apply,
    finite_lattice_boltzmannWeight_gaugeInvariant]

/-- The concrete finite-volume Euclidean Yang--Mills measure associated with the
Wilson action. -/
def FiniteLatticeWilsonSystem.gibbsMeasure
    (L : FiniteLatticeWilsonSystem) : Measure L.Configuration :=
  L.gibbsPMF.toMeasure

/-- The Wilson Gibbs measure is a genuine probability measure. -/
instance finiteLatticeWilsonSystem_gibbsMeasure_isProbabilityMeasure
    (L : FiniteLatticeWilsonSystem) :
    IsProbabilityMeasure L.gibbsMeasure := by
  unfold FiniteLatticeWilsonSystem.gibbsMeasure
  infer_instance

/-- The mass assigned to a single configuration is the normalized Boltzmann
weight. -/
theorem finite_lattice_gibbsMeasure_singleton
    (L : FiniteLatticeWilsonSystem) (A : L.Configuration) :
    L.gibbsMeasure ({A} : Set L.Configuration) =
      L.boltzmannWeight A * L.partitionFunction⁻¹ := by
  rw [FiniteLatticeWilsonSystem.gibbsMeasure,
    L.gibbsPMF.toMeasure_apply_singleton A (measurableSet_singleton A)]
  exact finite_lattice_gibbsPMF_apply L A

/-- Gauge invariance of all singleton masses; on this finite discrete
configuration space these singleton masses determine the entire measure. -/
theorem finite_lattice_gibbsMeasure_singleton_gaugeInvariant
    (L : FiniteLatticeWilsonSystem)
    (γ : L.GaugeTransformation) (A : L.Configuration) :
    L.gibbsMeasure ({L.gaugeTransform γ A} : Set L.Configuration) =
      L.gibbsMeasure ({A} : Set L.Configuration) := by
  rw [finite_lattice_gibbsMeasure_singleton,
    finite_lattice_gibbsMeasure_singleton,
    finite_lattice_boltzmannWeight_gaugeInvariant]

/-- A family of concrete finite-lattice Wilson systems forming the finite-volume
input of the existing continuum construction spine.  Reflection positivity and
Euclidean covariance remain explicit analytic obligations, while the measures
and their gauge invariance are now constructed rather than postulated. -/
structure FiniteLatticeWilsonApproximationFamily where
  index : Type
  system : index → FiniteLatticeWilsonSystem
  latticeSpacing : index → ℝ
  volumeScale : index → ℝ
  finiteVolumeReflectionPositive : Prop
  finiteVolumeReflectionPositive_proof : finiteVolumeReflectionPositive
  finiteVolumeEuclideanCovariant : Prop
  finiteVolumeEuclideanCovariant_proof : finiteVolumeEuclideanCovariant

/-- The concrete Wilson family induces the existing finite-volume approximation
surface with actual Mathlib probability measures. -/
def FiniteLatticeWilsonApproximationFamily.toFiniteVolumeApproximation
    (F : FiniteLatticeWilsonApproximationFamily) :
    EuclideanYangMillsFiniteVolumeApproximation :=
  { index := F.index
    finiteVolumeConfiguration := fun i => (F.system i).Configuration
    finiteVolumeMeasurableSpace := fun _i => inferInstance
    finiteVolumeMeasure := fun i => (F.system i).gibbsMeasure
    latticeSpacing := F.latticeSpacing
    volumeScale := F.volumeScale
    gaugeInvariantFiniteVolume :=
      ∀ i (γ : (F.system i).GaugeTransformation)
        (A : (F.system i).Configuration),
        (F.system i).gibbsMeasure
            ({(F.system i).gaugeTransform γ A} : Set (F.system i).Configuration) =
          (F.system i).gibbsMeasure ({A} : Set (F.system i).Configuration)
    gaugeInvariantFiniteVolume_proof := fun i γ A =>
      finite_lattice_gibbsMeasure_singleton_gaugeInvariant (F.system i) γ A
    finiteVolumeReflectionPositive := F.finiteVolumeReflectionPositive
    finiteVolumeReflectionPositive_proof := F.finiteVolumeReflectionPositive_proof
    finiteVolumeEuclideanCovariant := F.finiteVolumeEuclideanCovariant
    finiteVolumeEuclideanCovariant_proof := F.finiteVolumeEuclideanCovariant_proof
    finiteVolumeSchwingerData := fun _n => ℝ }

/-- The finite-volume measures in the induced approximation are probability
measures, by construction from normalized PMFs. -/
theorem finite_lattice_wilson_family_probability_measure
    (F : FiniteLatticeWilsonApproximationFamily) (i : F.index) :
    IsProbabilityMeasure
      (F.toFiniteVolumeApproximation.finiteVolumeMeasure
        (show F.toFiniteVolumeApproximation.index from i)) := by
  change IsProbabilityMeasure (F.system i).gibbsMeasure
  infer_instance

end

end MathlibAnalytic
end MGAP4D
