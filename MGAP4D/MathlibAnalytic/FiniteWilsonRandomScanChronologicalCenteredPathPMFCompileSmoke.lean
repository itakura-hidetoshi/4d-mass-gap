import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanChronologicalCenteredPathPMF

namespace MGAP4D
namespace MathlibAnalytic

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    (L.randomScanChronologicalCenteredFinitePathPMF (n + 1)).map
        linearMarkovChronologicalCenteredFinitePathInit =
      L.randomScanChronologicalCenteredFinitePathPMF n :=
  finite_lattice_randomScanChronologicalCenteredFinitePathPMF_succ_map_init
    L n

end MathlibAnalytic
end MGAP4D
