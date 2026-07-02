import MGAP4D.MathlibAnalytic.PeriodicHypercubicPlaquetteOrientationConnectivity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A canonical coordinate plane containing a supplied axis. Axis zero uses the
zero-one plane; every other axis is paired with axis zero and canonically sorted. -/
def periodicHypercubicAxisPairContaining
    (rho : PeriodicHypercubicAxis) : PeriodicHypercubicAxisPair :=
  if h : rho = 0 then
    periodicHypercubicAxisPairOfNe 0 1 (by decide)
  else
    periodicHypercubicAxisPairOfNe rho 0 (Ne.symm h)

/-- The canonical plane selected for an axis really contains that axis. -/
theorem periodicHypercubicAxisPairContaining_contains
    (rho : PeriodicHypercubicAxis) :
    periodicHypercubicAxisPairContains
      (periodicHypercubicAxisPairContaining rho) rho := by
  fin_cases rho <;>
    simp [periodicHypercubicAxisPairContaining,
      periodicHypercubicAxisPairContains,
      periodicHypercubicAxisPairOfNe]

/-- If a coordinate axis belongs to a plaquette plane, a positive unit shift in
that axis is reachable by one shared-link plaquette edge. -/
theorem periodicHypercubicPlaquetteGraph_reachable_shift_of_contains
    (n : Nat) (hn : 2 ≤ n)
    (x : PeriodicHypercubicVertex n)
    (pair : PeriodicHypercubicAxisPair)
    (rho : PeriodicHypercubicAxis)
    (hrho : periodicHypercubicAxisPairContains pair rho) :
    (periodicHypercubicPlaquetteGraph n).Reachable
      (x, pair) (periodicHypercubicShift n x rho, pair) := by
  rcases hrho with hfirst | hsecond
  · subst rho
    exact (periodicHypercubicPlaquetteAdjacent_shift_first
      n hn (x, pair)).reachable
  · subst rho
    exact (periodicHypercubicPlaquetteAdjacent_shift_second
      n hn (x, pair)).reachable

/-- Every positive unit coordinate shift of a periodic plaquette is reachable.
The path first changes to a plane containing the requested axis, performs the
unit shift, and then restores the original plane orientation. -/
theorem periodicHypercubicPlaquetteGraph_reachable_shift_axis
    (n : Nat) (hn : 2 ≤ n)
    (p : PeriodicHypercubicPlaquette n)
    (rho : PeriodicHypercubicAxis) :
    (periodicHypercubicPlaquetteGraph n).Reachable p
      (periodicHypercubicShift n p.1 rho, p.2) := by
  rcases p with ⟨x, pair⟩
  let carrier := periodicHypercubicAxisPairContaining rho
  have hToCarrier :
      (periodicHypercubicPlaquetteGraph n).Reachable
        (x, pair) (x, carrier) :=
    periodicHypercubicPlaquetteGraph_reachable_same_base n x pair carrier
  have hShift :
      (periodicHypercubicPlaquetteGraph n).Reachable
        (x, carrier) (periodicHypercubicShift n x rho, carrier) :=
    periodicHypercubicPlaquetteGraph_reachable_shift_of_contains
      n hn x carrier rho
        (periodicHypercubicAxisPairContaining_contains rho)
  have hRestore :
      (periodicHypercubicPlaquetteGraph n).Reachable
        (periodicHypercubicShift n x rho, carrier)
        (periodicHypercubicShift n x rho, pair) :=
    periodicHypercubicPlaquetteGraph_reachable_same_base
      n (periodicHypercubicShift n x rho) carrier pair
  exact hToCarrier.trans (hShift.trans hRestore)

/-- Consequently, the extended graph distance to every positive unit coordinate
shift is finite. -/
theorem periodicHypercubicPlaquetteEDistance_shift_axis_ne_top
    (n : Nat) (hn : 2 ≤ n)
    (p : PeriodicHypercubicPlaquette n)
    (rho : PeriodicHypercubicAxis) :
    periodicHypercubicPlaquetteEDistance n p
      (periodicHypercubicShift n p.1 rho, p.2) ≠ ⊤ := by
  apply SimpleGraph.edist_ne_top_iff_reachable.mpr
  exact periodicHypercubicPlaquetteGraph_reachable_shift_axis n hn p rho

end

end MathlibAnalytic
end MGAP4D
