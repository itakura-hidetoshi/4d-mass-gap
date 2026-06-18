import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The four coordinate axes of the Euclidean lattice. -/
abbrev PeriodicHypercubicAxis : Type := Fin 4

/-- Vertices of the periodic four-dimensional box of side length `n`. -/
abbrev PeriodicHypercubicVertex (n : ℕ) : Type :=
  PeriodicHypercubicAxis → ZMod n

/-- A physical positively oriented link is specified by its initial vertex and
coordinate direction.  Reverse traversal is represented separately at the
boundary-incidence level, rather than by duplicating the physical link. -/
abbrev PeriodicHypercubicEdge (n : ℕ) : Type :=
  PeriodicHypercubicVertex n × PeriodicHypercubicAxis

/-- Ordered coordinate-plane labels.  The strict order chooses each geometric
coordinate plane exactly once. -/
abbrev PeriodicHypercubicAxisPair : Type :=
  {pair : PeriodicHypercubicAxis × PeriodicHypercubicAxis // pair.1 < pair.2}

/-- A positively based plaquette is a vertex together with an ordered pair of
distinct coordinate axes. -/
abbrev PeriodicHypercubicPlaquette (n : ℕ) : Type :=
  PeriodicHypercubicVertex n × PeriodicHypercubicAxisPair

/-- Unit displacement in one coordinate direction. -/
def periodicHypercubicUnit
    (n : ℕ) (mu : PeriodicHypercubicAxis) :
    PeriodicHypercubicVertex n :=
  fun i => if i = mu then 1 else 0

/-- Periodic translation by one lattice unit. -/
def periodicHypercubicShift
    (n : ℕ)
    (x : PeriodicHypercubicVertex n)
    (mu : PeriodicHypercubicAxis) :
    PeriodicHypercubicVertex n :=
  x + periodicHypercubicUnit n mu

@[simp]
theorem periodicHypercubicShift_apply
    (n : ℕ)
    (x : PeriodicHypercubicVertex n)
    (mu i : PeriodicHypercubicAxis) :
    periodicHypercubicShift n x mu i =
      x i + if i = mu then 1 else 0 :=
  rfl

/-- Coordinate translations commute. -/
theorem periodicHypercubicShift_comm
    (n : ℕ)
    (x : PeriodicHypercubicVertex n)
    (mu nu : PeriodicHypercubicAxis) :
    periodicHypercubicShift n
        (periodicHypercubicShift n x mu) nu =
      periodicHypercubicShift n
        (periodicHypercubicShift n x nu) mu := by
  unfold periodicHypercubicShift
  abel

/-- Direction in which a physical positive link is traversed by a plaquette
boundary. -/
inductive PeriodicHypercubicOrientation where
  | forward
  | backward
  deriving DecidableEq, Fintype

/-- A signed incidence of a physical link in a plaquette boundary. -/
structure PeriodicHypercubicBoundaryStep (n : ℕ) where
  edge : PeriodicHypercubicEdge n
  orientation : PeriodicHypercubicOrientation
  deriving DecidableEq

/-- Initial endpoint of a physical positive link. -/
def periodicHypercubicEdgeSource
    (n : ℕ) (e : PeriodicHypercubicEdge n) :
    PeriodicHypercubicVertex n :=
  e.1

/-- Final endpoint of a physical positive link. -/
def periodicHypercubicEdgeTarget
    (n : ℕ) (e : PeriodicHypercubicEdge n) :
    PeriodicHypercubicVertex n :=
  periodicHypercubicShift n e.1 e.2

/-- Initial endpoint of a signed boundary step. -/
def PeriodicHypercubicBoundaryStep.source
    {n : ℕ} (s : PeriodicHypercubicBoundaryStep n) :
    PeriodicHypercubicVertex n :=
  match s.orientation with
  | .forward => periodicHypercubicEdgeSource n s.edge
  | .backward => periodicHypercubicEdgeTarget n s.edge

/-- Final endpoint of a signed boundary step. -/
def PeriodicHypercubicBoundaryStep.target
    {n : ℕ} (s : PeriodicHypercubicBoundaryStep n) :
    PeriodicHypercubicVertex n :=
  match s.orientation with
  | .forward => periodicHypercubicEdgeTarget n s.edge
  | .backward => periodicHypercubicEdgeSource n s.edge

/-- First coordinate direction of a plaquette. -/
def periodicHypercubicPlaquetteFirstAxis
    {n : ℕ} (p : PeriodicHypercubicPlaquette n) :
    PeriodicHypercubicAxis :=
  p.2.1.1

/-- Second coordinate direction of a plaquette. -/
def periodicHypercubicPlaquetteSecondAxis
    {n : ℕ} (p : PeriodicHypercubicPlaquette n) :
    PeriodicHypercubicAxis :=
  p.2.1.2

/-- The two plaquette directions are distinct. -/
theorem periodicHypercubicPlaquette_axes_ne
    {n : ℕ} (p : PeriodicHypercubicPlaquette n) :
    periodicHypercubicPlaquetteFirstAxis p ≠
      periodicHypercubicPlaquetteSecondAxis p :=
  ne_of_lt p.2.2

/-- The standard signed four-step boundary of a periodic coordinate plaquette:
`+mu`, `+nu`, `-mu`, `-nu`. -/
def periodicHypercubicBoundaryStep
    (n : ℕ)
    (p : PeriodicHypercubicPlaquette n)
    (k : Fin 4) :
    PeriodicHypercubicBoundaryStep n :=
  let x := p.1
  let mu := periodicHypercubicPlaquetteFirstAxis p
  let nu := periodicHypercubicPlaquetteSecondAxis p
  match k.1 with
  | 0 => ⟨(x, mu), .forward⟩
  | 1 => ⟨(periodicHypercubicShift n x mu, nu), .forward⟩
  | 2 => ⟨(periodicHypercubicShift n x nu, mu), .backward⟩
  | _ => ⟨(x, nu), .backward⟩

@[simp]
theorem periodicHypercubicBoundaryStep_zero
    (n : ℕ) (p : PeriodicHypercubicPlaquette n) :
    periodicHypercubicBoundaryStep n p 0 =
      ⟨(p.1, periodicHypercubicPlaquetteFirstAxis p), .forward⟩ :=
  rfl

@[simp]
theorem periodicHypercubicBoundaryStep_one
    (n : ℕ) (p : PeriodicHypercubicPlaquette n) :
    periodicHypercubicBoundaryStep n p 1 =
      ⟨(periodicHypercubicShift n p.1
          (periodicHypercubicPlaquetteFirstAxis p),
        periodicHypercubicPlaquetteSecondAxis p), .forward⟩ :=
  rfl

@[simp]
theorem periodicHypercubicBoundaryStep_two
    (n : ℕ) (p : PeriodicHypercubicPlaquette n) :
    periodicHypercubicBoundaryStep n p 2 =
      ⟨(periodicHypercubicShift n p.1
          (periodicHypercubicPlaquetteSecondAxis p),
        periodicHypercubicPlaquetteFirstAxis p), .backward⟩ :=
  rfl

@[simp]
theorem periodicHypercubicBoundaryStep_three
    (n : ℕ) (p : PeriodicHypercubicPlaquette n) :
    periodicHypercubicBoundaryStep n p 3 =
      ⟨(p.1, periodicHypercubicPlaquetteSecondAxis p), .backward⟩ :=
  rfl

/-- The first and second signed boundary steps meet. -/
theorem periodicHypercubic_boundary_cycle_01
    (n : ℕ) (p : PeriodicHypercubicPlaquette n) :
    (periodicHypercubicBoundaryStep n p 0).target =
      (periodicHypercubicBoundaryStep n p 1).source :=
  rfl

/-- The second and third signed boundary steps meet; this is precisely the
commutativity of independent coordinate translations. -/
theorem periodicHypercubic_boundary_cycle_12
    (n : ℕ) (p : PeriodicHypercubicPlaquette n) :
    (periodicHypercubicBoundaryStep n p 1).target =
      (periodicHypercubicBoundaryStep n p 2).source := by
  simpa [PeriodicHypercubicBoundaryStep.source,
    PeriodicHypercubicBoundaryStep.target,
    periodicHypercubicEdgeSource, periodicHypercubicEdgeTarget] using
    periodicHypercubicShift_comm n p.1
      (periodicHypercubicPlaquetteFirstAxis p)
      (periodicHypercubicPlaquetteSecondAxis p)

/-- The third and fourth signed boundary steps meet. -/
theorem periodicHypercubic_boundary_cycle_23
    (n : ℕ) (p : PeriodicHypercubicPlaquette n) :
    (periodicHypercubicBoundaryStep n p 2).target =
      (periodicHypercubicBoundaryStep n p 3).source :=
  rfl

/-- The fourth signed boundary step closes the plaquette. -/
theorem periodicHypercubic_boundary_cycle_30
    (n : ℕ) (p : PeriodicHypercubicPlaquette n) :
    (periodicHypercubicBoundaryStep n p 3).target =
      (periodicHypercubicBoundaryStep n p 0).source :=
  rfl

/-- Value contributed by one signed boundary incidence. -/
def periodicHypercubicStepValue
    {n : ℕ} {Gauge : Type} [Group Gauge]
    (A : PeriodicHypercubicEdge n → Gauge)
    (s : PeriodicHypercubicBoundaryStep n) : Gauge :=
  match s.orientation with
  | .forward => A s.edge
  | .backward => (A s.edge)⁻¹

/-- Gauge transformation of a physical positive link. -/
def periodicHypercubicGaugeTransform
    {n : ℕ} {Gauge : Type} [Group Gauge]
    (gamma : PeriodicHypercubicVertex n → Gauge)
    (A : PeriodicHypercubicEdge n → Gauge) :
    PeriodicHypercubicEdge n → Gauge :=
  fun e => gamma (periodicHypercubicEdgeSource n e) * A e *
    (gamma (periodicHypercubicEdgeTarget n e))⁻¹

/-- A signed boundary step transforms by its actual oriented endpoints. -/
theorem periodicHypercubicStepValue_gaugeTransform
    {n : ℕ} {Gauge : Type} [Group Gauge]
    (gamma : PeriodicHypercubicVertex n → Gauge)
    (A : PeriodicHypercubicEdge n → Gauge)
    (s : PeriodicHypercubicBoundaryStep n) :
    periodicHypercubicStepValue
        (periodicHypercubicGaugeTransform gamma A) s =
      gamma s.source * periodicHypercubicStepValue A s *
        (gamma s.target)⁻¹ := by
  cases s with
  | mk edge orientation =>
      cases orientation <;>
        simp [periodicHypercubicStepValue,
          periodicHypercubicGaugeTransform,
          PeriodicHypercubicBoundaryStep.source,
          PeriodicHypercubicBoundaryStep.target,
          periodicHypercubicEdgeSource,
          periodicHypercubicEdgeTarget] <;>
        group

/-- Ordered signed plaquette holonomy. -/
def periodicHypercubicPlaquetteHolonomy
    {n : ℕ} {Gauge : Type} [Group Gauge]
    (A : PeriodicHypercubicEdge n → Gauge)
    (p : PeriodicHypercubicPlaquette n) : Gauge :=
  periodicHypercubicStepValue A (periodicHypercubicBoundaryStep n p 0) *
    periodicHypercubicStepValue A (periodicHypercubicBoundaryStep n p 1) *
    periodicHypercubicStepValue A (periodicHypercubicBoundaryStep n p 2) *
    periodicHypercubicStepValue A (periodicHypercubicBoundaryStep n p 3)

/-- The signed periodic plaquette holonomy transforms by conjugation at its
initial vertex. -/
theorem periodicHypercubicPlaquetteHolonomy_gaugeTransform
    {n : ℕ} {Gauge : Type} [Group Gauge]
    (gamma : PeriodicHypercubicVertex n → Gauge)
    (A : PeriodicHypercubicEdge n → Gauge)
    (p : PeriodicHypercubicPlaquette n) :
    periodicHypercubicPlaquetteHolonomy
        (periodicHypercubicGaugeTransform gamma A) p =
      gamma p.1 * periodicHypercubicPlaquetteHolonomy A p *
        (gamma p.1)⁻¹ := by
  unfold periodicHypercubicPlaquetteHolonomy
  rw [periodicHypercubicStepValue_gaugeTransform,
    periodicHypercubicStepValue_gaugeTransform,
    periodicHypercubicStepValue_gaugeTransform,
    periodicHypercubicStepValue_gaugeTransform]
  rw [periodicHypercubic_boundary_cycle_01 n p,
    periodicHypercubic_boundary_cycle_12 n p,
    periodicHypercubic_boundary_cycle_23 n p,
    periodicHypercubic_boundary_cycle_30 n p]
  simp [PeriodicHypercubicBoundaryStep.source,
    periodicHypercubicEdgeSource]
  group

end

end MathlibAnalytic
end MGAP4D
