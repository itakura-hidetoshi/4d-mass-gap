import MGAP4D.MathlibAnalytic.PeriodicHypercubicPlaquetteNeighborBound
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The simple graph whose vertices are periodic hypercubic plaquettes and whose
edges record shared physical boundary links. -/
def periodicHypercubicPlaquetteGraph
    (n : Nat) :
    SimpleGraph (PeriodicHypercubicPlaquette n) :=
  { Adj := periodicHypercubicPlaquetteAdjacent n
    symm := periodicHypercubicPlaquetteAdjacent_symmetric n
    loopless := { irrefl := fun p h => h.1 rfl } }

/-- The graph adjacency relation is definitionally the concrete shared-link
plaquette adjacency relation. -/
@[simp] theorem periodicHypercubicPlaquetteGraph_adj_iff
    (n : Nat)
    (p q : PeriodicHypercubicPlaquette n) :
    (periodicHypercubicPlaquetteGraph n).Adj p q ↔
      periodicHypercubicPlaquetteAdjacent n p q :=
  Iff.rfl

/-- Extended shortest-path distance from a selected periodic plaquette. It is
infinite until graph connectedness is supplied, avoiding the disconnected
junk value of the Nat-valued graph distance. -/
noncomputable def periodicHypercubicPlaquetteEDistance
    (n : Nat)
    (selected p : PeriodicHypercubicPlaquette n) : ℕ∞ :=
  (periodicHypercubicPlaquetteGraph n).edist selected p

/-- A selected plaquette has extended graph distance zero from itself. -/
@[simp] theorem periodicHypercubicPlaquetteEDistance_self
    (n : Nat)
    (selected : PeriodicHypercubicPlaquette n) :
    periodicHypercubicPlaquetteEDistance n selected selected = 0 := by
  simp [periodicHypercubicPlaquetteEDistance]

/-- Extended graph distance one is exactly concrete shared-link adjacency. -/
theorem periodicHypercubicPlaquetteEDistance_eq_one_iff
    (n : Nat)
    (selected p : PeriodicHypercubicPlaquette n) :
    periodicHypercubicPlaquetteEDistance n selected p = 1 ↔
      periodicHypercubicPlaquetteAdjacent n selected p := by
  change (periodicHypercubicPlaquetteGraph n).edist selected p = 1 ↔ _
  rw [SimpleGraph.edist_eq_one_iff_adj]
  rfl

end

end MathlibAnalytic
end MGAP4D
