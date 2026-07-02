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

end

end MathlibAnalytic
end MGAP4D
