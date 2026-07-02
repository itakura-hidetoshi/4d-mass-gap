import MGAP4D.MathlibAnalytic.PeriodicHypercubicPlaquetteGraphConnectivity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicPlaquetteCardinality
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The natural-number shortest-path distance between periodic hypercubic
plaquettes. Connectedness for side length at least two makes this distance
non-junk in all subsequent uses. -/
noncomputable def periodicHypercubicPlaquetteDistance
    (n : Nat)
    (selected p : PeriodicHypercubicPlaquette n) : Nat :=
  (periodicHypercubicPlaquetteGraph n).dist selected p

/-- The natural plaquette distance from a selected plaquette to itself is zero. -/
@[simp] theorem periodicHypercubicPlaquetteDistance_self
    (n : Nat)
    (selected : PeriodicHypercubicPlaquette n) :
    periodicHypercubicPlaquetteDistance n selected selected = 0 := by
  simp [periodicHypercubicPlaquetteDistance]

/-- On the connected periodic plaquette graph, the natural-number distance
coerces exactly to the previously defined extended distance. -/
theorem periodicHypercubicPlaquetteDistance_coe_eq_EDistance
    (n : Nat) (hn : 2 ≤ n)
    (selected p : PeriodicHypercubicPlaquette n) :
    (periodicHypercubicPlaquetteDistance n selected p : ℕ∞) =
      periodicHypercubicPlaquetteEDistance n selected p := by
  exact
    (periodicHypercubicPlaquetteGraph_connected n hn selected p).coe_dist_eq_edist

/-- A shortest-path distance in the finite connected plaquette graph is strictly
smaller than the total number of plaquettes. -/
theorem periodicHypercubicPlaquetteDistance_lt_card
    (n : Nat) (hn : 2 ≤ n)
    (selected p : PeriodicHypercubicPlaquette n) :
    periodicHypercubicPlaquetteDistance n selected p <
      Fintype.card (PeriodicHypercubicPlaquette n) := by
  let hConnected := periodicHypercubicPlaquetteGraph_connected n hn
  obtain ⟨w, hw⟩ := (hConnected selected p).exists_isPath
  calc
    periodicHypercubicPlaquetteDistance n selected p ≤ w.length := by
      exact SimpleGraph.dist_le w
    _ < Fintype.card (PeriodicHypercubicPlaquette n) := hw.length_lt

/-- Explicit finite radius containing every periodic plaquette around any
selected plaquette. -/
def periodicHypercubicPlaquetteDistanceRadius (n : Nat) : Nat :=
  6 * n ^ 4

/-- Every periodic plaquette lies at distance below the explicit radius
`6 * n^4`, the exact number of positively based coordinate plaquettes. -/
theorem periodicHypercubicPlaquetteDistance_lt_radius
    (n : Nat) (hn : 2 ≤ n)
    (selected p : PeriodicHypercubicPlaquette n) :
    periodicHypercubicPlaquetteDistance n selected p <
      periodicHypercubicPlaquetteDistanceRadius n := by
  have hPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  letI : NeZero n := ⟨Nat.ne_of_gt hPos⟩
  rw [periodicHypercubicPlaquetteDistanceRadius,
    ← periodicHypercubicPlaquette_card n]
  exact periodicHypercubicPlaquetteDistance_lt_card n hn selected p

/-- The finite shell at graph distance `m` from a selected periodic plaquette. -/
noncomputable def periodicHypercubicPlaquetteDistanceShell
    (n : Nat)
    (selected : PeriodicHypercubicPlaquette n)
    (m : Nat) : Finset (PeriodicHypercubicPlaquette n) := by
  classical
  exact Finset.univ.filter fun p =>
    periodicHypercubicPlaquetteDistance n selected p = m

/-- Membership in the explicit distance shell is exactly equality of the
natural plaquette distance with the shell index. -/
@[simp] theorem periodicHypercubic_mem_distanceShell_iff
    (n : Nat)
    (selected p : PeriodicHypercubicPlaquette n)
    (m : Nat) :
    p ∈ periodicHypercubicPlaquetteDistanceShell n selected m ↔
      periodicHypercubicPlaquetteDistance n selected p = m := by
  classical
  simp [periodicHypercubicPlaquetteDistanceShell]

end

end MathlibAnalytic
end MGAP4D
