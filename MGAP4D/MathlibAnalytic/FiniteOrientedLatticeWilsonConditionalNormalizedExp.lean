import MGAP4D.MathlibAnalytic.FiniteNormalizedExponentialOscillation
import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonConditionalRemoteCancellation

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- Real log-weight of the exact target-local oriented Wilson conditional. -/
def FiniteOrientedLatticeWilsonSystem.targetLocalSingleLinkLogWeight
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge)
    (g : L.Gauge) : ℝ :=
  -L.beta *
    L.targetLocalPlaquetteAction (L.replaceLink A target g) target

end

end MathlibAnalytic
end MGAP4D
