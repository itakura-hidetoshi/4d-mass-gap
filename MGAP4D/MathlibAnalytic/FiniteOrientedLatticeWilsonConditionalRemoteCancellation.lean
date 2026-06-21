import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonConditionalWeightFactorization

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- Partition function of the target-local conditional factors. -/
def FiniteOrientedLatticeWilsonSystem.targetLocalSingleLinkPartitionFunction
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge) : ℝ≥0∞ :=
  ∑' g : L.Gauge,
    L.targetLocalSingleLinkBoltzmannWeight A target g

end

end MathlibAnalytic
end MGAP4D
