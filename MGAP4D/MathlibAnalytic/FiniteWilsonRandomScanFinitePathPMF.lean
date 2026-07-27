import MGAP4D.MathlibAnalytic.LinearMarkovFinitePathPMF
import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanPMFStationarity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- The arbitrary-length finite path PMF of the actual finite Wilson random-scan
single-link heat-bath chain, started in the finite Gibbs PMF. The parameter `n`
is the number of transitions, so paths have `n + 1` coordinates. -/
def FiniteLatticeWilsonSystem.randomScanFinitePathPMF
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) : PMF (Fin (n + 1) → L.Configuration) :=
  linearMarkovFinitePathPMF L.gibbsPMF L.randomScanTransitionPMF n

/-- Deleting the terminal coordinate from the actual finite Wilson path PMF
recovers the preceding path PMF. -/
theorem finite_lattice_randomScanFinitePathPMF_succ_map_init
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    (L.randomScanFinitePathPMF (n + 1)).map Fin.init =
      L.randomScanFinitePathPMF n := by
  unfold FiniteLatticeWilsonSystem.randomScanFinitePathPMF
  exact
    linearMarkovFinitePathPMF_succ_map_init
      L.gibbsPMF L.randomScanTransitionPMF n

/-- Every time coordinate of every Gibbs-started actual finite Wilson
random-scan path PMF has exactly the finite Gibbs PMF as its marginal. -/
theorem finite_lattice_randomScanFinitePathPMF_map_eval
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (i : Fin (n + 1)) :
    (L.randomScanFinitePathPMF n).map (fun path => path i) =
      L.gibbsPMF := by
  unfold FiniteLatticeWilsonSystem.randomScanFinitePathPMF
  exact
    linearMarkovFinitePathPMF_map_eval_of_expectation_stationary
      L.gibbsPMF L.randomScanTransitionPMF
      (finite_lattice_randomScanTransitionPMF_gibbs_expectation_stationary L)
      n i

/-- In particular, the terminal coordinate of every Gibbs-started actual finite
Wilson random-scan path PMF has the finite Gibbs PMF as its marginal. -/
theorem finite_lattice_randomScanFinitePathPMF_map_last
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    (L.randomScanFinitePathPMF n).map
        (fun path => path (Fin.last n)) =
      L.gibbsPMF :=
  finite_lattice_randomScanFinitePathPMF_map_eval L n (Fin.last n)

/-- Every point probability of every actual finite Wilson random-scan finite
path PMF is nonnegative. -/
theorem finite_lattice_randomScanFinitePathPMF_nonneg
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (path : Fin (n + 1) → L.Configuration) :
    0 ≤ L.randomScanFinitePathPMF n path :=
  bot_le

end

end MathlibAnalytic
end MGAP4D
