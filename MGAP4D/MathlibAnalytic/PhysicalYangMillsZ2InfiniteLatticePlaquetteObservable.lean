import MGAP4D.MathlibAnalytic.PhysicalYangMillsZ2PeriodicInfiniteLatticeCarrier
import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonPlaquetteObservableVariation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A positively based coordinate plaquette of the integer four-dimensional
hypercubic lattice. -/
abbrev IntegerHypercubicPlaquette : Type :=
  IntegerHypercubicVertex × PeriodicHypercubicAxisPair

/-- First direction of an integer-lattice plaquette. -/
def integerHypercubicPlaquetteFirstAxis
    (p : IntegerHypercubicPlaquette) : Fin 4 :=
  p.2.1.1

/-- Second direction of an integer-lattice plaquette. -/
def integerHypercubicPlaquetteSecondAxis
    (p : IntegerHypercubicPlaquette) : Fin 4 :=
  p.2.1.2

/-- Integer unit displacement in one coordinate direction. -/
def integerHypercubicUnit
    (mu : Fin 4) : IntegerHypercubicVertex :=
  fun i => if i = mu then 1 else 0

/-- Translation by one integer lattice unit. -/
def integerHypercubicShift
    (x : IntegerHypercubicVertex)
    (mu : Fin 4) : IntegerHypercubicVertex :=
  x + integerHypercubicUnit mu

/-- The four physical positive links in the standard signed plaquette boundary.
Indices two and three are traversed backwards by the holonomy. -/
def integerHypercubicPlaquetteBoundaryEdge
    (p : IntegerHypercubicPlaquette)
    (k : Fin 4) : IntegerHypercubicEdge :=
  let x := p.1
  let mu := integerHypercubicPlaquetteFirstAxis p
  let nu := integerHypercubicPlaquetteSecondAxis p
  match k.1 with
  | 0 => (x, mu)
  | 1 => (integerHypercubicShift x mu, nu)
  | 2 => (integerHypercubicShift x nu, mu)
  | _ => (x, nu)

/-- Four Boolean link coordinates read by one integer-lattice plaquette. -/
def z2InfiniteHypercubicPlaquetteCoordinates
    (B : Z2InfiniteHypercubicBinaryConfiguration)
    (p : IntegerHypercubicPlaquette) : Fin 4 → Bool :=
  fun k =>
    z2InfiniteHypercubicBinaryConfigurationRead B
      (integerHypercubicPlaquetteBoundaryEdge p k)

/-- The `Z₂` Wilson plaquette energy of four boundary-link bits. -/
def z2InfiniteHypercubicPlaquetteEnergyOfBits
    (b : Fin 4 → Bool) : ℝ :=
  if boolEquivZ2Gauge (b 0) *
        boolEquivZ2Gauge (b 1) *
        (boolEquivZ2Gauge (b 2))⁻¹ *
        (boolEquivZ2Gauge (b 3))⁻¹ = 1
  then 0
  else 1

/-- Reading one encoded integer link is continuous in the product topology. -/
theorem z2InfiniteHypercubicBinaryConfigurationRead_continuous
    (e : IntegerHypercubicEdge) :
    Continuous
      (fun B : Z2InfiniteHypercubicBinaryConfiguration =>
        z2InfiniteHypercubicBinaryConfigurationRead B e) := by
  simpa [z2InfiniteHypercubicBinaryConfigurationRead] using
    (continuous_apply (Encodable.encode e) :
      Continuous
        (fun B : Z2InfiniteHypercubicBinaryConfiguration =>
          B (Encodable.encode e)))

/-- The four-coordinate restriction map of one plaquette is continuous. -/
theorem z2InfiniteHypercubicPlaquetteCoordinates_continuous
    (p : IntegerHypercubicPlaquette) :
    Continuous
      (fun B : Z2InfiniteHypercubicBinaryConfiguration =>
        z2InfiniteHypercubicPlaquetteCoordinates B p) := by
  apply continuous_pi
  intro k
  exact z2InfiniteHypercubicBinaryConfigurationRead_continuous
    (integerHypercubicPlaquetteBoundaryEdge p k)

/-- The finite four-bit Wilson energy is continuous. -/
theorem z2InfiniteHypercubicPlaquetteEnergyOfBits_continuous :
    Continuous z2InfiniteHypercubicPlaquetteEnergyOfBits :=
  continuous_of_discreteTopology

/-- A bounded continuous local plaquette observable on the concrete compact
infinite-lattice binary carrier. -/
noncomputable def z2InfiniteHypercubicPlaquetteObservable
    (p : IntegerHypercubicPlaquette) :
    BoundedContinuousFunction
      Z2InfiniteHypercubicBinaryConfiguration ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun B =>
        z2InfiniteHypercubicPlaquetteEnergyOfBits
          (z2InfiniteHypercubicPlaquetteCoordinates B p),
      z2InfiniteHypercubicPlaquetteEnergyOfBits_continuous.comp
        (z2InfiniteHypercubicPlaquetteCoordinates_continuous p)⟩

@[simp]
theorem z2InfiniteHypercubicPlaquetteObservable_apply
    (p : IntegerHypercubicPlaquette)
    (B : Z2InfiniteHypercubicBinaryConfiguration) :
    z2InfiniteHypercubicPlaquetteObservable p B =
      z2InfiniteHypercubicPlaquetteEnergyOfBits
        (z2InfiniteHypercubicPlaquetteCoordinates B p) :=
  rfl

/-- Reduction modulo a periodic side length commutes with one coordinate shift. -/
theorem integerHypercubicVertexToPeriodic_shift
    (n : ℕ)
    (x : IntegerHypercubicVertex)
    (mu : Fin 4) :
    integerHypercubicVertexToPeriodic n (integerHypercubicShift x mu) =
      periodicHypercubicShift n
        (integerHypercubicVertexToPeriodic n x) mu := by
  funext i
  simp [integerHypercubicVertexToPeriodic, integerHypercubicShift,
    integerHypercubicUnit, periodicHypercubicShift,
    periodicHypercubicUnit]

/-- Reduce an integer plaquette to the corresponding periodic plaquette. -/
def integerHypercubicPlaquetteToPeriodic
    (n : ℕ)
    (p : IntegerHypercubicPlaquette) :
    PeriodicHypercubicPlaquette n :=
  (integerHypercubicVertexToPeriodic n p.1, p.2)

/-- Every physical boundary link reduces to the matching periodic boundary
link. -/
theorem integerHypercubicPlaquetteBoundaryEdge_toPeriodic
    (n : ℕ)
    (p : IntegerHypercubicPlaquette)
    (k : Fin 4) :
    integerHypercubicEdgeToPeriodic n
        (integerHypercubicPlaquetteBoundaryEdge p k) =
      (periodicHypercubicBoundaryStep n
        (integerHypercubicPlaquetteToPeriodic n p) k).edge := by
  fin_cases k <;>
    simp [integerHypercubicPlaquetteBoundaryEdge,
      integerHypercubicPlaquetteToPeriodic,
      integerHypercubicPlaquetteFirstAxis,
      integerHypercubicPlaquetteSecondAxis,
      periodicHypercubicPlaquetteFirstAxis,
      periodicHypercubicPlaquetteSecondAxis,
      integerHypercubicEdgeToPeriodic,
      integerHypercubicVertexToPeriodic_shift]

/-- The local observable on the common carrier pulls back exactly to the finite
periodic `Z₂` plaquette observable at every volume. -/
theorem z2InfiniteHypercubicPlaquetteObservable_pullback
    (n : ℕ) [NeZero n]
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (p : IntegerHypercubicPlaquette)
    (A :
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta).Configuration) :
    z2InfiniteHypercubicPlaquetteObservable p
        (z2PeriodicHypercubicConfigurationExtend n A) =
      FiniteOrientedLatticeWilsonSystem.plaquetteObservable
        (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
        (integerHypercubicPlaquetteToPeriodic n p) A := by
  have hCoordinate :
      ∀ k : Fin 4,
        boolEquivZ2Gauge
            (z2InfiniteHypercubicPlaquetteCoordinates
              (z2PeriodicHypercubicConfigurationExtend n A) p k) =
          A ((periodicHypercubicBoundaryStep n
            (integerHypercubicPlaquetteToPeriodic n p) k).edge) := by
    intro k
    simp [z2InfiniteHypercubicPlaquetteCoordinates,
      integerHypercubicPlaquetteBoundaryEdge_toPeriodic]
  change
    z2InfiniteHypercubicPlaquetteEnergyOfBits
        (z2InfiniteHypercubicPlaquetteCoordinates
          (z2PeriodicHypercubicConfigurationExtend n A) p) = _
  unfold z2InfiniteHypercubicPlaquetteEnergyOfBits
  rw [hCoordinate 0, hCoordinate 1, hCoordinate 2, hCoordinate 3]
  rfl

end

end MathlibAnalytic
end MGAP4D
