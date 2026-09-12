import MGAP4D.MathlibAnalytic.LinearMarkovInfinitePathShiftInvariance
import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanInfinitePathMeasure
import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanPMFStationarity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Deleting the initial coordinate of an actual finite Wilson random-scan path
recovers the preceding finite path PMF. -/
theorem finite_lattice_randomScanFinitePathPMF_succ_map_tail
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    (L.randomScanFinitePathPMF (n + 1)).map
        (linearMarkovFinitePathTail (n := n)) =
      L.randomScanFinitePathPMF n := by
  unfold FiniteLatticeWilsonSystem.randomScanFinitePathPMF
  exact
    linearMarkovFinitePathPMF_succ_map_tail_of_expectation_stationary
      L.gibbsPMF L.randomScanTransitionPMF
      (finite_lattice_randomScanTransitionPMF_gibbs_expectation_stationary L)
      n

/-- Every finite prefix of the shifted infinite Wilson path law is exactly the
corresponding Gibbs-started finite Wilson path measure. -/
theorem finite_lattice_randomScanInfinitePathMeasure_map_shift_map_finPrefix
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    (L.randomScanInfinitePathMeasure.map linearMarkovPathShift).map
        (linearMarkovInfinitePathFinPrefix n) =
      (L.randomScanFinitePathPMF n).toMeasure := by
  unfold FiniteLatticeWilsonSystem.randomScanInfinitePathMeasure
    FiniteLatticeWilsonSystem.randomScanFinitePathPMF
  exact
    linearMarkovInfinitePathMeasure_map_shift_map_finPrefix
      L.gibbsPMF L.randomScanTransitionPMF
      (finite_lattice_randomScanTransitionPMF_gibbs_expectation_stationary L)
      n

/-- The actual stationary infinite finite-Wilson random-scan path law is
invariant under the full left shift on natural-time path space. -/
theorem finite_lattice_randomScanInfinitePathMeasure_map_shift
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    L.randomScanInfinitePathMeasure.map linearMarkovPathShift =
      L.randomScanInfinitePathMeasure := by
  unfold FiniteLatticeWilsonSystem.randomScanInfinitePathMeasure
  exact
    linearMarkovInfinitePathMeasure_map_shift_of_expectation_stationary
      L.gibbsPMF L.randomScanTransitionPMF
      (finite_lattice_randomScanTransitionPMF_gibbs_expectation_stationary L)

end

end MathlibAnalytic
end MGAP4D
