import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonGibbsMeasure

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Orientation with which a physical positive link is traversed in a
plaquette boundary. -/
inductive FiniteBoundaryOrientation where
  | forward
  | backward
  deriving DecidableEq, Fintype

/-- One signed boundary incidence of a physical link.  The physical link is
not duplicated in the configuration space; only its traversal orientation is
recorded here. -/
structure FiniteOrientedBoundaryStep (Edge : Type) where
  edge : Edge
  orientation : FiniteBoundaryOrientation
  deriving DecidableEq

/-- Initial endpoint of a signed traversal of a physical positive link. -/
def FiniteOrientedBoundaryStep.initial
    {Vertex Edge : Type}
    (edgeSource edgeTarget : Edge → Vertex)
    (step : FiniteOrientedBoundaryStep Edge) : Vertex :=
  match step.orientation with
  | .forward => edgeSource step.edge
  | .backward => edgeTarget step.edge

/-- Final endpoint of a signed traversal of a physical positive link. -/
def FiniteOrientedBoundaryStep.terminal
    {Vertex Edge : Type}
    (edgeSource edgeTarget : Edge → Vertex)
    (step : FiniteOrientedBoundaryStep Edge) : Vertex :=
  match step.orientation with
  | .forward => edgeTarget step.edge
  | .backward => edgeSource step.edge

/-- A finite Wilson system whose configurations live on physical positive
links while each plaquette boundary records whether that physical link is
traversed forward or backward.

This is the orientation-correct counterpart of `FiniteLatticeWilsonSystem`.
It prevents reverse traversals from becoming independent configuration
variables. -/
structure FiniteOrientedLatticeWilsonSystem where
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
  edgeSource : Edge → Vertex
  edgeTarget : Edge → Vertex
  boundary : Plaquette → Fin 4 → FiniteOrientedBoundaryStep Edge
  boundary_cycle_01 : ∀ p,
    (boundary p 0).terminal edgeSource edgeTarget =
      (boundary p 1).initial edgeSource edgeTarget
  boundary_cycle_12 : ∀ p,
    (boundary p 1).terminal edgeSource edgeTarget =
      (boundary p 2).initial edgeSource edgeTarget
  boundary_cycle_23 : ∀ p,
    (boundary p 2).terminal edgeSource edgeTarget =
      (boundary p 3).initial edgeSource edgeTarget
  boundary_cycle_30 : ∀ p,
    (boundary p 3).terminal edgeSource edgeTarget =
      (boundary p 0).initial edgeSource edgeTarget
  plaquetteEnergy : Gauge → ℝ
  plaquetteEnergy_nonneg : ∀ g, 0 ≤ plaquetteEnergy g
  plaquetteEnergy_conjInvariant :
    ∀ h g, plaquetteEnergy (h * g * h⁻¹) = plaquetteEnergy g
  beta : ℝ
  beta_nonneg : 0 ≤ beta

attribute [instance]
  FiniteOrientedLatticeWilsonSystem.gaugeGroup
  FiniteOrientedLatticeWilsonSystem.gaugeFintype
  FiniteOrientedLatticeWilsonSystem.gaugeInhabited
  FiniteOrientedLatticeWilsonSystem.gaugeNontrivial
  FiniteOrientedLatticeWilsonSystem.gaugeMeasurableSpace
  FiniteOrientedLatticeWilsonSystem.gaugeMeasurableSingleton
  FiniteOrientedLatticeWilsonSystem.vertexFintype
  FiniteOrientedLatticeWilsonSystem.edgeFintype
  FiniteOrientedLatticeWilsonSystem.plaquetteFintype

/-- Gauge configurations assign one group element to each physical positive
link. -/
abbrev FiniteOrientedLatticeWilsonSystem.Configuration
    (L : FiniteOrientedLatticeWilsonSystem) : Type :=
  L.Edge → L.Gauge

/-- Vertex gauge transformations. -/
abbrev FiniteOrientedLatticeWilsonSystem.GaugeTransformation
    (L : FiniteOrientedLatticeWilsonSystem) : Type :=
  L.Vertex → L.Gauge

/-- The ordinary left-right gauge action on physical positive links. -/
def FiniteOrientedLatticeWilsonSystem.gaugeTransform
    (L : FiniteOrientedLatticeWilsonSystem)
    (gamma : L.GaugeTransformation)
    (A : L.Configuration) : L.Configuration :=
  fun e => gamma (L.edgeSource e) * A e *
    (gamma (L.edgeTarget e))⁻¹

/-- Group value contributed by one signed boundary incidence. -/
def FiniteOrientedLatticeWilsonSystem.stepValue
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (step : FiniteOrientedBoundaryStep L.Edge) : L.Gauge :=
  match step.orientation with
  | .forward => A step.edge
  | .backward => (A step.edge)⁻¹

/-- A signed incidence transforms using its actual oriented endpoints. -/
theorem finite_oriented_stepValue_gaugeTransform
    (L : FiniteOrientedLatticeWilsonSystem)
    (gamma : L.GaugeTransformation)
    (A : L.Configuration)
    (step : FiniteOrientedBoundaryStep L.Edge) :
    L.stepValue (L.gaugeTransform gamma A) step =
      gamma (step.initial L.edgeSource L.edgeTarget) *
        L.stepValue A step *
        (gamma (step.terminal L.edgeSource L.edgeTarget))⁻¹ := by
  cases step with
  | mk edge orientation =>
      cases orientation <;>
        simp [FiniteOrientedLatticeWilsonSystem.stepValue,
          FiniteOrientedLatticeWilsonSystem.gaugeTransform,
          FiniteOrientedBoundaryStep.initial,
          FiniteOrientedBoundaryStep.terminal] <;>
        group

/-- Ordered signed plaquette holonomy. -/
def FiniteOrientedLatticeWilsonSystem.plaquetteHolonomy
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (p : L.Plaquette) : L.Gauge :=
  L.stepValue A (L.boundary p 0) *
    L.stepValue A (L.boundary p 1) *
    L.stepValue A (L.boundary p 2) *
    L.stepValue A (L.boundary p 3)

/-- Signed plaquette holonomy transforms by conjugation at its initial vertex. -/
theorem finite_oriented_plaquetteHolonomy_gaugeTransform
    (L : FiniteOrientedLatticeWilsonSystem)
    (gamma : L.GaugeTransformation)
    (A : L.Configuration)
    (p : L.Plaquette) :
    L.plquetteHolonomy (L.gaugeTransform gamma A) p =
      gamma ((L.boundary p 0).initial L.edgeSource L.edgeTarget) *
        L.plquetteHolonomy A p *
        (gamma ((L.boundary p 0).initial
          L.edgeSource L.edgeTarget))⁻¹ := by
  unfold FiniteOrientedLatticeWilsonSystem.plquetteHolonomy
  rw [finite_oriented_stepValue_gaugeTransform,
    finite_oriented_stepValue_gaugeTransform,
    finite_oriented_stepValue_gaugeTransform,
    finite_oriented_stepValue_gaugeTransform]
  rw [L.boundary_cycle_01 p, L.boundary_cycle_12 p,
    L.boundary_cycle_23 p, L.boundary_cycle_30 p]
  group

/-- Wilson action of an orientation-correct finite system. -/
def FiniteOrientedLatticeWilsonSystem.wilsonAction
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration) : ℝ :=
  ∑ p : L.Plaquette,
    L.plaquetteEnergy (L.plquetteHolonomy A p)

/-- The orientation-correct Wilson action is nonnegative. -/
theorem finite_oriented_wilsonAction_nonneg
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration) :
    0 ≤ L.wilsonAction A := by
  unfold FiniteOrientedLatticeWilsonSystem.wilsonAction
  exact Finset.sum_nonneg fun p _ => L.plaquetteEnergy_nonneg _

/-- Gauge invariance of the orientation-correct Wilson action. -/
theorem finite_oriented_wilsonAction_gaugeInvariant
    (L : FiniteOrientedLatticeWilsonSystem)
    (gamma : L.GaugeTransformation)
    (A : L.Configuration) :
    L.wilsonAction (L.gaugeTransform gamma A) = L.wilsonAction A := by
  unfold FiniteOrientedLatticeWilsonSystem.wilsonAction
  apply Finset.sum_congr rfl
  intro p _hp
  rw [finite_oriented_plaquetteHolonomy_gaugeTransform]
  exact L.plaquetteEnergy_conjInvariant _ _

/-- A plaquette touches a physical link when one signed boundary incidence
projects to that link. -/
def FiniteOrientedLatticeWilsonSystem.PlaquetteTouchesEdge
    (L : FiniteOrientedLatticeWilsonSystem)
    (p : L.Plaquette)
    (e : L.Edge) : Prop :=
  ∃ k : Fin 4, (L.boundary p k).edge = e

/-- Physical links sharing at least one plaquette with a target link. -/
noncomputable def FiniteOrientedLatticeWilsonSystem.plaquetteNeighbors
    (L : FiniteOrientedLatticeWilsonSystem)
    (target : L.Edge) : Finset L.Edge := by
  classical
  exact Finset.univ.filter fun source =>
    ∃ p : L.Plaquette,
      L.PlaquetteTouchesEdge p target ∧
        L.PlaquetteTouchesEdge p source

/-- Geometrically active links, with the zero diagonal removed. -/
noncomputable def FiniteOrientedLatticeWilsonSystem.activePlaquetteNeighbors
    (L : FiniteOrientedLatticeWilsonSystem)
    (target : L.Edge) : Finset L.Edge := by
  classical
  exact (L.plaquetteNeighbors target).erase target

/-- Plaquettes touching both physical links. -/
noncomputable def FiniteOrientedLatticeWilsonSystem.sharedPlaquettes
    (L : FiniteOrientedLatticeWilsonSystem)
    (target source : L.Edge) : Finset L.Plaquette := by
  classical
  exact Finset.univ.filter fun p =>
    L.PlaquetteTouchesEdge p target ∧
      L.PlaquetteTouchesEdge p source

@[simp] theorem finite_oriented_mem_plaquetteNeighbors_iff
    (L : FiniteOrientedLatticeWilsonSystem)
    (target source : L.Edge) :
    source ∈ L.plaquetteNeighbors target ↔
      ∃ p : L.Plaquette,
        L.PlaquetteTouchesEdge p target ∧
          L.PlaquetteTouchesEdge p source := by
  classical
  simp [FiniteOrientedLatticeWilsonSystem.plaquetteNeighbors]

@[simp] theorem finite_oriented_mem_activePlaquetteNeighbors_iff
    (L : FiniteOrientedLatticeWilsonSystem)
    (target source : L.Edge) :
    source ∈ L.activePlaquetteNeighbors target ↔
      (∃ p : L.Plaquette,
        L.PlaquetteTouchesEdge p target ∧
          L.PlaquetteTouchesEdge p source) ∧
        source ≠ target := by
  classical
  simp [FiniteOrientedLatticeWilsonSystem.activePlaquetteNeighbors,
    finite_oriented_mem_plaquetteNeighbors_iff, and_comm]

@[simp] theorem finite_oriented_mem_sharedPlaquettes_iff
    (L : FiniteOrientedLatticeWilsonSystem)
    (target source : L.Edge)
    (p : L.Plaquette) :
    p ∈ L.sharedPlaquettes target source ↔
      L.PlaquetteTouchesEdge p target ∧
        L.PlaquetteTouchesEdge p source := by
  classical
  simp [FiniteOrientedLatticeWilsonSystem.sharedPlaquettes]

end

end MathlibAnalytic
end MGAP4D
