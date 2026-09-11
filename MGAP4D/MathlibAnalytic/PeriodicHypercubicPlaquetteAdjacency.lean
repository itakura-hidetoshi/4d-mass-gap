import MGAP4D.MathlibAnalytic.PeriodicHypercubicPlaquetteIncidenceSupport

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Two distinct periodic hypercubic plaquettes are adjacent when they share a
physical boundary link. -/
def periodicHypercubicPlaquetteAdjacent
    (n : Nat)
    (p q : PeriodicHypercubicPlaquette n) : Prop :=
  And (Not (p = q))
    (Exists fun e : PeriodicHypercubicEdge n =>
      And (periodicHypercubicPlaquetteTouchesEdge n p e)
        (periodicHypercubicPlaquetteTouchesEdge n q e))

/-- A shared physical boundary link constructs plaquette adjacency. -/
theorem periodicHypercubicPlaquetteAdjacent_of_shared_edge
    (n : Nat)
    {p q : PeriodicHypercubicPlaquette n}
    (hne : Not (p = q))
    (e : PeriodicHypercubicEdge n)
    (hp : periodicHypercubicPlaquetteTouchesEdge n p e)
    (hq : periodicHypercubicPlaquetteTouchesEdge n q e) :
    periodicHypercubicPlaquetteAdjacent n p q :=
  And.intro hne (Exists.intro e (And.intro hp hq))

/-- Adjacent periodic plaquettes are distinct. -/
theorem periodicHypercubicPlaquetteAdjacent_ne
    (n : Nat)
    {p q : PeriodicHypercubicPlaquette n}
    (h : periodicHypercubicPlaquetteAdjacent n p q) :
    Not (p = q) :=
  h.1

/-- Plaquette adjacency through a shared physical link is symmetric. -/
theorem periodicHypercubicPlaquetteAdjacent_symm
    (n : Nat)
    {p q : PeriodicHypercubicPlaquette n}
    (h : periodicHypercubicPlaquetteAdjacent n p q) :
    periodicHypercubicPlaquetteAdjacent n q p := by
  refine And.intro ?_ ?_
  · intro hqp
    exact h.1 hqp.symm
  · exact Exists.elim h.2 (fun e he =>
      Exists.intro e (And.intro he.2 he.1))

/-- The concrete periodic plaquette adjacency relation is symmetric. -/
theorem periodicHypercubicPlaquetteAdjacent_symmetric
    (n : Nat) :
    Symmetric (periodicHypercubicPlaquetteAdjacent n) := by
  intro p q h
  exact periodicHypercubicPlaquetteAdjacent_symm n h

end

end MathlibAnalytic
end MGAP4D
