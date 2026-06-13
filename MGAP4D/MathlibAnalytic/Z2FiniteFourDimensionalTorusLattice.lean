import MGAP4D.MathlibAnalytic.Z2FiniteFourDimensionalHypercubicPlaquetteGeometry
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Vertices of a finite four-dimensional periodic lattice with side length
`N + 1` in every direction. -/
abbrev FiniteFourTorusVertex (N : ℕ) : Type :=
  Fin 4 → ZMod (N + 1)

/-- Directed edges are represented by their ordered pair of endpoints. -/
abbrev FiniteFourTorusEdge (N : ℕ) : Type :=
  FiniteFourTorusVertex N × FiniteFourTorusVertex N

/-- An ordered pair of distinct lattice directions. -/
abbrev FiniteFourTorusDirectionPair : Type :=
  {d : Fin 4 × Fin 4 // d.1 ≠ d.2}

/-- A plaquette is specified by a base vertex and two distinct directions. -/
abbrev FiniteFourTorusPlaquette (N : ℕ) : Type :=
  FiniteFourTorusVertex N × FiniteFourTorusDirectionPair

/-- Positive unit vector in one of the four periodic directions. -/
def finiteFourTorusUnitStep (N : ℕ) (μ : Fin 4) :
    FiniteFourTorusVertex N :=
  fun i => if i = μ then 1 else 0

/-- Periodic unit translation of a vertex. -/
def finiteFourTorusStep
    (N : ℕ) (v : FiniteFourTorusVertex N) (μ : Fin 4) :
    FiniteFourTorusVertex N :=
  v + finiteFourTorusUnitStep N μ

/-- Base vertex of a torus plaquette. -/
def finiteFourTorusPlaquetteBase
    {N : ℕ} (p : FiniteFourTorusPlaquette N) :
    FiniteFourTorusVertex N :=
  p.1

/-- First direction of a torus plaquette. -/
def finiteFourTorusPlaquetteFirstDirection
    {N : ℕ} (p : FiniteFourTorusPlaquette N) : Fin 4 :=
  p.2.1.1

/-- Second direction of a torus plaquette. -/
def finiteFourTorusPlaquetteSecondDirection
    {N : ℕ} (p : FiniteFourTorusPlaquette N) : Fin 4 :=
  p.2.1.2

/-- The two directions defining a torus plaquette are distinct. -/
theorem finiteFourTorusPlaquette_directions_ne
    {N : ℕ} (p : FiniteFourTorusPlaquette N) :
    finiteFourTorusPlaquetteFirstDirection p ≠
      finiteFourTorusPlaquetteSecondDirection p :=
  p.2.2

/-- Four ordered corners of a positively oriented torus plaquette. -/
def finiteFourTorusPlaquetteCorner00
    {N : ℕ} (p : FiniteFourTorusPlaquette N) :
    FiniteFourTorusVertex N :=
  finiteFourTorusPlaquetteBase p

def finiteFourTorusPlaquetteCorner10
    {N : ℕ} (p : FiniteFourTorusPlaquette N) :
    FiniteFourTorusVertex N :=
  finiteFourTorusStep N (finiteFourTorusPlaquetteBase p)
    (finiteFourTorusPlaquetteFirstDirection p)

def finiteFourTorusPlaquetteCorner11
    {N : ℕ} (p : FiniteFourTorusPlaquette N) :
    FiniteFourTorusVertex N :=
  finiteFourTorusStep N
    (finiteFourTorusPlaquetteCorner10 p)
    (finiteFourTorusPlaquetteSecondDirection p)

def finiteFourTorusPlaquetteCorner01
    {N : ℕ} (p : FiniteFourTorusPlaquette N) :
    FiniteFourTorusVertex N :=
  finiteFourTorusStep N (finiteFourTorusPlaquetteBase p)
    (finiteFourTorusPlaquetteSecondDirection p)

/-- Ordered vertex support of a torus plaquette. -/
def finiteFourTorusPlaquetteVertices
    {N : ℕ} (p : FiniteFourTorusPlaquette N) :
    List (FiniteFourTorusVertex N) :=
  [finiteFourTorusPlaquetteCorner00 p,
    finiteFourTorusPlaquetteCorner10 p,
    finiteFourTorusPlaquetteCorner11 p,
    finiteFourTorusPlaquetteCorner01 p]

/-- Source and target maps for endpoint-pair edges. -/
def finiteFourTorusEdgeSource
    {N : ℕ} (e : FiniteFourTorusEdge N) : FiniteFourTorusVertex N :=
  e.1

def finiteFourTorusEdgeTarget
    {N : ℕ} (e : FiniteFourTorusEdge N) : FiniteFourTorusVertex N :=
  e.2

/-- Four directed boundary edges of a torus plaquette.  The third and fourth
edges are oriented back toward the base vertex.  Explicit equality tests avoid
relying on tactic-generated elimination from `Fin 4`. -/
def finiteFourTorusPlaquetteBoundary
    {N : ℕ} (p : FiniteFourTorusPlaquette N) (k : Fin 4) :
    FiniteFourTorusEdge N :=
  if k = 0 then
    (finiteFourTorusPlaquetteCorner00 p,
      finiteFourTorusPlaquetteCorner10 p)
  else if k = 1 then
    (finiteFourTorusPlaquetteCorner10 p,
      finiteFourTorusPlaquetteCorner11 p)
  else if k = 2 then
    (finiteFourTorusPlaquetteCorner11 p,
      finiteFourTorusPlaquetteCorner01 p)
  else
    (finiteFourTorusPlaquetteCorner01 p,
      finiteFourTorusPlaquetteCorner00 p)

@[simp]
theorem finiteFourTorus_boundary_cycle_01
    {N : ℕ} (p : FiniteFourTorusPlaquette N) :
    finiteFourTorusEdgeTarget (finiteFourTorusPlaquetteBoundary p 0) =
      finiteFourTorusEdgeSource (finiteFourTorusPlaquetteBoundary p 1) := by
  simp [finiteFourTorusPlaquetteBoundary,
    finiteFourTorusEdgeTarget, finiteFourTorusEdgeSource]

@[simp]
theorem finiteFourTorus_boundary_cycle_12
    {N : ℕ} (p : FiniteFourTorusPlaquette N) :
    finiteFourTorusEdgeTarget (finiteFourTorusPlaquetteBoundary p 1) =
      finiteFourTorusEdgeSource (finiteFourTorusPlaquetteBoundary p 2) := by
  simp [finiteFourTorusPlaquetteBoundary,
    finiteFourTorusEdgeTarget, finiteFourTorusEdgeSource]

@[simp]
theorem finiteFourTorus_boundary_cycle_23
    {N : ℕ} (p : FiniteFourTorusPlaquette N) :
    finiteFourTorusEdgeTarget (finiteFourTorusPlaquetteBoundary p 2) =
      finiteFourTorusEdgeSource (finiteFourTorusPlaquetteBoundary p 3) := by
  simp [finiteFourTorusPlaquetteBoundary,
    finiteFourTorusEdgeTarget, finiteFourTorusEdgeSource]

@[simp]
theorem finiteFourTorus_boundary_cycle_30
    {N : ℕ} (p : FiniteFourTorusPlaquette N) :
    finiteFourTorusEdgeTarget (finiteFourTorusPlaquetteBoundary p 3) =
      finiteFourTorusEdgeSource (finiteFourTorusPlaquetteBoundary p 0) := by
  simp [finiteFourTorusPlaquetteBoundary,
    finiteFourTorusEdgeTarget, finiteFourTorusEdgeSource]

/-- Concrete finite four-dimensional periodic `Z₂` Wilson system. -/
def finiteFourTorusZ2WilsonSystem
    (N : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergyIdentity : 0 ≤ energyIdentity)
    (hEnergyNontrivial : 0 ≤ energyNontrivial) :
    FiniteLatticeWilsonSystem :=
  z2FiniteLatticeWilsonSystem
    (FiniteFourTorusVertex N)
    (FiniteFourTorusEdge N)
    (FiniteFourTorusPlaquette N)
    finiteFourTorusEdgeSource
    finiteFourTorusEdgeTarget
    finiteFourTorusPlaquetteBoundary
    finiteFourTorus_boundary_cycle_01
    finiteFourTorus_boundary_cycle_12
    finiteFourTorus_boundary_cycle_23
    finiteFourTorus_boundary_cycle_30
    β energyIdentity energyNontrivial
    hβ hEnergyIdentity hEnergyNontrivial

/-- The concrete system has the expected periodic four-dimensional carrier. -/
theorem finiteFourTorusZ2WilsonSystem_vertex_eq
    (N : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergyIdentity : 0 ≤ energyIdentity)
    (hEnergyNontrivial : 0 ≤ energyNontrivial) :
    (finiteFourTorusZ2WilsonSystem N β energyIdentity energyNontrivial
      hβ hEnergyIdentity hEnergyNontrivial).Vertex =
      FiniteFourTorusVertex N :=
  rfl

end

end MathlibAnalytic
end MGAP4D
