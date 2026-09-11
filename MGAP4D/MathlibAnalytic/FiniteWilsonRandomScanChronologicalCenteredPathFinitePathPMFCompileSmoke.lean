import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanChronologicalCenteredPathFinitePathPMF

namespace MGAP4D
namespace MathlibAnalytic

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    L.randomScanChronologicalCenteredFinitePathPMF n =
      L.randomScanFinitePathPMF (2 * n + 2) :=
  finite_lattice_randomScanChronologicalCenteredFinitePathPMF_eq_finitePathPMF
    L n

end MathlibAnalytic
end MGAP4D
