import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanIntegerCenteredPathProjectiveFamily

namespace MGAP4D
namespace MathlibAnalytic

example (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n d : ℕ) :
    (L.randomScanFinitePathPMF (2 * (n + d) + 2)).map
      (linearMarkovIntegerCenteredFinitePathRestrictBy n d) =
        L.randomScanFinitePathPMF (2 * n + 2) :=
  finite_lattice_randomScanFinitePathPMF_map_integerCenteredRestrictBy
    L n d

end MathlibAnalytic
end MGAP4D
