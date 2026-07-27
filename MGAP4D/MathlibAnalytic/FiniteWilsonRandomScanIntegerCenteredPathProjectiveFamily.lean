import MGAP4D.MathlibAnalytic.LinearMarkovIntegerCenteredPathProjectiveFamily
import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanChronologicalCenteredPathFinitePathPMF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The actual finite Wilson random-scan path on the symmetric integer interval
`[-n-1, n+1]`. -/
abbrev FiniteLatticeWilsonSystem.RandomScanIntegerCenteredFinitePath
    (L : FiniteLatticeWilsonSystem)
    (n : ℕ) :=
  LinearMarkovIntegerCenteredFinitePath L.Configuration n

/-- The actual Gibbs-stationary random-scan law on `[-n-1, n+1]`. -/
abbrev FiniteLatticeWilsonSystem.randomScanIntegerCenteredFinitePathPMF
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    PMF (L.RandomScanIntegerCenteredFinitePath n) :=
  linearMarkovIntegerCenteredFinitePathPMF
    L.gibbsPMF L.randomScanTransitionPMF n

/-- Every larger actual Wilson symmetric integer interval restricts exactly to
any smaller one. -/
theorem finite_lattice_randomScanIntegerCenteredFinitePathPMF_map_restrictBy
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n d : ℕ) :
    (L.randomScanIntegerCenteredFinitePathPMF (n + d)).map
      (linearMarkovIntegerCenteredFinitePathRestrictBy n d) =
        L.randomScanIntegerCenteredFinitePathPMF n := by
  exact
    linearMarkovIntegerCenteredFinitePathPMF_map_restrictBy_of_detailedBalance
      L.gibbsPMF L.randomScanTransitionPMF
        (finite_lattice_randomScanDetailedBalanceReal L) n d

/-- Equivalently, the ordinary Gibbs-started random-scan finite path laws are
consistent under the centered integer-interval restrictions. -/
theorem finite_lattice_randomScanFinitePathPMF_map_integerCenteredRestrictBy
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n d : ℕ) :
    (L.randomScanFinitePathPMF (2 * (n + d) + 2)).map
      (linearMarkovIntegerCenteredFinitePathRestrictBy n d) =
        L.randomScanFinitePathPMF (2 * n + 2) := by
  exact
    linearMarkovFinitePathPMF_map_integerCenteredRestrictBy_of_detailedBalance
      L.gibbsPMF L.randomScanTransitionPMF
        (finite_lattice_randomScanDetailedBalanceReal L) n d

end

end MathlibAnalytic
end MGAP4D
