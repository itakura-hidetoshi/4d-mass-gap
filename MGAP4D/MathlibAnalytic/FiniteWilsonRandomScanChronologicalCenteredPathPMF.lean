import MGAP4D.MathlibAnalytic.LinearMarkovChronologicalCenteredPathConsistency
import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanSingleChainCenteredTimeReflectionPMF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- One actual finite Wilson random-scan segment written chronologically around
time zero. -/
abbrev FiniteLatticeWilsonSystem.RandomScanChronologicalCenteredFinitePath
    (L : FiniteLatticeWilsonSystem)
    (n : ℕ) :=
  LinearMarkovChronologicalCenteredFinitePath L.Configuration n

/-- The actual Gibbs-stationary random-scan law on the explicit chronological
carrier `Fin (2 * n + 3) → Configuration`. -/
abbrev FiniteLatticeWilsonSystem.randomScanChronologicalCenteredFinitePathPMF
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    PMF (L.RandomScanChronologicalCenteredFinitePath n) :=
  linearMarkovChronologicalCenteredFinitePathPMF
    L.gibbsPMF L.randomScanTransitionPMF n

/-- Unpacking the actual chronological Wilson law recovers the previously
constructed centered reflected/positive path law exactly. -/
theorem finite_lattice_randomScanChronologicalCenteredFinitePathPMF_map_unpack
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    (L.randomScanChronologicalCenteredFinitePathPMF n).map
        linearMarkovChronologicalToCenteredFinitePath =
      L.randomScanCenteredFinitePathPMF n := by
  exact
    linearMarkovChronologicalCenteredFinitePathPMF_map_unpack_eq_centered
      L.gibbsPMF L.randomScanTransitionPMF
        (finite_lattice_randomScanDetailedBalanceReal L) n

/-- The explicit chronological Wilson path laws are projectively consistent:
removing the oldest negative-time coordinate and latest positive-time coordinate
from horizon `n + 1` gives exactly horizon `n`. -/
theorem finite_lattice_randomScanChronologicalCenteredFinitePathPMF_succ_map_init
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    (L.randomScanChronologicalCenteredFinitePathPMF (n + 1)).map
        linearMarkovChronologicalCenteredFinitePathInit =
      L.randomScanChronologicalCenteredFinitePathPMF n := by
  exact
    linearMarkovChronologicalCenteredFinitePathPMF_succ_map_init_of_detailedBalance
      L.gibbsPMF L.randomScanTransitionPMF
        (finite_lattice_randomScanDetailedBalanceReal L) n

end

end MathlibAnalytic
end MGAP4D
