import MGAP4D.MathlibAnalytic.LinearMarkovChronologicalCenteredPathFinitePathPMF
import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanChronologicalCenteredPathPMF
import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanFinitePathPMF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The actual chronological finite Wilson random-scan law is exactly the
ordinary Gibbs-started random-scan finite-path PMF with `2 * n + 2`
transitions. -/
theorem finite_lattice_randomScanChronologicalCenteredFinitePathPMF_eq_finitePathPMF
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    L.randomScanChronologicalCenteredFinitePathPMF n =
      L.randomScanFinitePathPMF (2 * n + 2) := by
  exact linearMarkovChronologicalCenteredFinitePathPMF_eq_finitePathPMF
    L.gibbsPMF L.randomScanTransitionPMF n

end

end MathlibAnalytic
end MGAP4D
