import MGAP4D.MathlibAnalytic.PeriodicHypercubicPlaquetteRepeatedAxisShift
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Adjust one coordinate of a periodic vertex to a target value by applying the
canonical positive unit shift the standard-residue number of times. -/
def periodicHypercubicAdjustCoordinate
    (n : Nat)
    (x y : PeriodicHypercubicVertex n)
    (rho : PeriodicHypercubicAxis) : PeriodicHypercubicVertex n :=
  periodicHypercubicShiftIterate n x rho (y rho - x rho).val

/-- Coordinate adjustment reaches the requested target value at the selected
axis. -/
theorem periodicHypercubicAdjustCoordinate_apply_self
    (n : Nat) [NeZero n]
    (x y : PeriodicHypercubicVertex n)
    (rho : PeriodicHypercubicAxis) :
    periodicHypercubicAdjustCoordinate n x y rho rho = y rho := by
  rw [periodicHypercubicAdjustCoordinate,
    periodicHypercubicShiftIterate_apply_self]
  have hcast :
      (((y rho - x rho).val : Nat) : ZMod n) = y rho - x rho := by
    simpa using
      (ZMod.natCast_val (R := ZMod n) (y rho - x rho))
  rw [hcast]
  abel

/-- Coordinate adjustment leaves every other axis unchanged. -/
theorem periodicHypercubicAdjustCoordinate_apply_of_ne
    (n : Nat)
    (x y : PeriodicHypercubicVertex n)
    (rho i : PeriodicHypercubicAxis)
    (h : i ≠ rho) :
    periodicHypercubicAdjustCoordinate n x y rho i = x i := by
  exact periodicHypercubicShiftIterate_apply_of_ne n x rho i h
    (y rho - x rho).val

/-- Adjusting one coordinate is reachable in the periodic plaquette graph. -/
theorem periodicHypercubicPlaquetteGraph_reachable_adjustCoordinate
    (n : Nat) (hn : 2 ≤ n)
    (x y : PeriodicHypercubicVertex n)
    (pair : PeriodicHypercubicAxisPair)
    (rho : PeriodicHypercubicAxis) :
    (periodicHypercubicPlaquetteGraph n).Reachable
      (x, pair) (periodicHypercubicAdjustCoordinate n x y rho, pair) := by
  exact periodicHypercubicPlaquetteGraph_reachable_shift_iterate
    n hn (x, pair) rho (y rho - x rho).val

/-- Successively adjust all four coordinates of a periodic vertex. -/
def periodicHypercubicAdjustAllCoordinates
    (n : Nat)
    (x y : PeriodicHypercubicVertex n) : PeriodicHypercubicVertex n :=
  let x0 := periodicHypercubicAdjustCoordinate n x y 0
  let x1 := periodicHypercubicAdjustCoordinate n x0 y 1
  let x2 := periodicHypercubicAdjustCoordinate n x1 y 2
  periodicHypercubicAdjustCoordinate n x2 y 3

/-- The four successive coordinate adjustments recover the target periodic
vertex exactly. -/
theorem periodicHypercubicAdjustAllCoordinates_eq
    (n : Nat) [NeZero n]
    (x y : PeriodicHypercubicVertex n) :
    periodicHypercubicAdjustAllCoordinates n x y = y := by
  funext i
  fin_cases i <;>
    simp [periodicHypercubicAdjustAllCoordinates,
      periodicHypercubicAdjustCoordinate_apply_self,
      periodicHypercubicAdjustCoordinate_apply_of_ne]

/-- Any two periodic plaquettes with the same plane orientation are reachable by
successively adjusting the four coordinates of the base vertex. -/
theorem periodicHypercubicPlaquetteGraph_reachable_same_orientation
    (n : Nat) (hn : 2 ≤ n)
    (x y : PeriodicHypercubicVertex n)
    (pair : PeriodicHypercubicAxisPair) :
    (periodicHypercubicPlaquetteGraph n).Reachable (x, pair) (y, pair) := by
  have hPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  letI : NeZero n := ⟨Nat.ne_of_gt hPos⟩
  let x0 := periodicHypercubicAdjustCoordinate n x y 0
  let x1 := periodicHypercubicAdjustCoordinate n x0 y 1
  let x2 := periodicHypercubicAdjustCoordinate n x1 y 2
  let x3 := periodicHypercubicAdjustCoordinate n x2 y 3
  have h0 :
      (periodicHypercubicPlaquetteGraph n).Reachable (x, pair) (x0, pair) :=
    periodicHypercubicPlaquetteGraph_reachable_adjustCoordinate
      n hn x y pair 0
  have h1 :
      (periodicHypercubicPlaquetteGraph n).Reachable (x0, pair) (x1, pair) :=
    periodicHypercubicPlaquetteGraph_reachable_adjustCoordinate
      n hn x0 y pair 1
  have h2 :
      (periodicHypercubicPlaquetteGraph n).Reachable (x1, pair) (x2, pair) :=
    periodicHypercubicPlaquetteGraph_reachable_adjustCoordinate
      n hn x1 y pair 2
  have h3 :
      (periodicHypercubicPlaquetteGraph n).Reachable (x2, pair) (x3, pair) :=
    periodicHypercubicPlaquetteGraph_reachable_adjustCoordinate
      n hn x2 y pair 3
  have hx3 : x3 = y := by
    simpa [x0, x1, x2, x3,
      periodicHypercubicAdjustAllCoordinates] using
      periodicHypercubicAdjustAllCoordinates_eq n x y
  simpa [hx3] using h0.trans (h1.trans (h2.trans h3))

/-- The shared-link periodic plaquette graph is connected for every side length
at least two. -/
theorem periodicHypercubicPlaquetteGraph_connected
    (n : Nat) (hn : 2 ≤ n) :
    (periodicHypercubicPlaquetteGraph n).Connected := by
  refine
    { preconnected := ?_
      nonempty := ⟨((fun _ => 0), periodicHypercubicAxisPairOfNe 0 1 (by decide))⟩ }
  intro p q
  rcases p with ⟨x, a⟩
  rcases q with ⟨y, b⟩
  have hBase :
      (periodicHypercubicPlaquetteGraph n).Reachable (x, a) (y, a) :=
    periodicHypercubicPlaquetteGraph_reachable_same_orientation n hn x y a
  have hOrientation :
      (periodicHypercubicPlaquetteGraph n).Reachable (y, a) (y, b) :=
    periodicHypercubicPlaquetteGraph_reachable_same_base n y a b
  exact hBase.trans hOrientation

/-- Hence every periodic plaquette has finite extended graph distance from every
other plaquette when the side length is at least two. -/
theorem periodicHypercubicPlaquetteEDistance_ne_top
    (n : Nat) (hn : 2 ≤ n)
    (p q : PeriodicHypercubicPlaquette n) :
    periodicHypercubicPlaquetteEDistance n p q ≠ ⊤ := by
  apply SimpleGraph.edist_ne_top_iff_reachable.mpr
  exact periodicHypercubicPlaquetteGraph_connected n hn p q

end

end MathlibAnalytic
end MGAP4D
