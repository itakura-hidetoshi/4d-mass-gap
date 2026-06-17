import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonCanonicalCenteredVariationProfile

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

noncomputable instance finiteLatticeWilsonEdgeDecidableEq
    (L : FiniteLatticeWilsonSystem) : DecidableEq L.Edge :=
  Classical.decEq L.Edge

end

end MathlibAnalytic
end MGAP4D
