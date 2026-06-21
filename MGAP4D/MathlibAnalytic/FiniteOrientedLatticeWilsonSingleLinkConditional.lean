import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonPlaquetteLocality

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- Exact single-link Boltzmann weight obtained by varying one physical link. -/
def FiniteOrientedLatticeWilsonSystem.singleLinkBoltzmannWeight
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge)
    (g : L.Gauge) : ℝ≥0∞ :=
  ENNReal.ofReal
    (Real.exp (-L.beta * L.wilsonAction (L.replaceLink A target g)))

end

end MathlibAnalytic
end MGAP4D
