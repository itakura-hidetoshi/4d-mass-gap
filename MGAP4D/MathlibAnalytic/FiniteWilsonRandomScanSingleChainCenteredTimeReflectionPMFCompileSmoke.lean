import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanSingleChainCenteredTimeReflectionPMF

namespace MGAP4D
namespace MathlibAnalytic

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    L.randomScanSingleChainCenteredFinitePathPMF n =
      L.randomScanCenteredFinitePathPMF n :=
  finite_lattice_randomScanSingleChainCenteredFinitePathPMF_eq_centered L n

end MathlibAnalytic
end MGAP4D
