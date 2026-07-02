import MGAP4D.MathlibAnalytic.PeriodicHypercubicPlaquetteGraphDistance
import MGAP4D.MathlibAnalytic.PeriodicHypercubicNondegenerateShifts
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Translating a periodic plaquette by one unit along its first coordinate axis
produces a shared-link adjacent plaquette when the side length is at least two. -/
theorem periodicHypercubicPlaquetteAdjacent_shift_first
    (n : Nat) (hn : 2 ≤ n)
    (p : PeriodicHypercubicPlaquette n) :
    periodicHypercubicPlaquetteAdjacent n p
      (periodicHypercubicShift n p.1
        (periodicHypercubicPlaquetteFirstAxis p), p.2) := by
  let q : PeriodicHypercubicPlaquette n :=
    (periodicHypercubicShift n p.1
      (periodicHypercubicPlaquetteFirstAxis p), p.2)
  have hne : p ≠ q := by
    intro h
    have hbase := congrArg Prod.fst h
    exact periodicHypercubicShift_ne_self n hn p.1
      (periodicHypercubicPlaquetteFirstAxis p) hbase.symm
  let e : PeriodicHypercubicEdge n :=
    (periodicHypercubicShift n p.1
      (periodicHypercubicPlaquetteFirstAxis p),
      periodicHypercubicPlaquetteSecondAxis p)
  apply periodicHypercubicPlaquetteAdjacent_of_shared_edge n hne e
  · exact ⟨1, rfl⟩
  · exact ⟨3, rfl⟩

/-- Translating a periodic plaquette by one unit along its second coordinate axis
produces a shared-link adjacent plaquette when the side length is at least two. -/
theorem periodicHypercubicPlaquetteAdjacent_shift_second
    (n : Nat) (hn : 2 ≤ n)
    (p : PeriodicHypercubicPlaquette n) :
    periodicHypercubicPlaquetteAdjacent n p
      (periodicHypercubicShift n p.1
        (periodicHypercubicPlaquetteSecondAxis p), p.2) := by
  let q : PeriodicHypercubicPlaquette n :=
    (periodicHypercubicShift n p.1
      (periodicHypercubicPlaquetteSecondAxis p), p.2)
  have hne : p ≠ q := by
    intro h
    have hbase := congrArg Prod.fst h
    exact periodicHypercubicShift_ne_self n hn p.1
      (periodicHypercubicPlaquetteSecondAxis p) hbase.symm
  let e : PeriodicHypercubicEdge n :=
    (periodicHypercubicShift n p.1
      (periodicHypercubicPlaquetteSecondAxis p),
      periodicHypercubicPlaquetteFirstAxis p)
  apply periodicHypercubicPlaquetteAdjacent_of_shared_edge n hne e
  · exact ⟨2, rfl⟩
  · exact ⟨0, rfl⟩

/-- The first-axis unit translate is at extended plaquette graph distance one. -/
theorem periodicHypercubicPlaquetteEDistance_shift_first
    (n : Nat) (hn : 2 ≤ n)
    (p : PeriodicHypercubicPlaquette n) :
    periodicHypercubicPlaquetteEDistance n p
      (periodicHypercubicShift n p.1
        (periodicHypercubicPlaquetteFirstAxis p), p.2) = 1 := by
  apply (periodicHypercubicPlaquetteEDistance_eq_one_iff n p _).2
  exact periodicHypercubicPlaquetteAdjacent_shift_first n hn p

/-- The second-axis unit translate is at extended plaquette graph distance one. -/
theorem periodicHypercubicPlaquetteEDistance_shift_second
    (n : Nat) (hn : 2 ≤ n)
    (p : PeriodicHypercubicPlaquette n) :
    periodicHypercubicPlaquetteEDistance n p
      (periodicHypercubicShift n p.1
        (periodicHypercubicPlaquetteSecondAxis p), p.2) = 1 := by
  apply (periodicHypercubicPlaquetteEDistance_eq_one_iff n p _).2
  exact periodicHypercubicPlaquetteAdjacent_shift_second n hn p

end

end MathlibAnalytic
end MGAP4D
