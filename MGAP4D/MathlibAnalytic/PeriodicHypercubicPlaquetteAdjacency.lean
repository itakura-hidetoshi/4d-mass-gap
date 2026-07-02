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

end

end MathlibAnalytic
end MGAP4D
