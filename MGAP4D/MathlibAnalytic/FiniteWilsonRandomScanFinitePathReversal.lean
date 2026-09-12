import MGAP4D.MathlibAnalytic.LinearMarkovFinitePathReversal
import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanDetailedBalancePairLaw
import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanFinitePathPMF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- Every point probability of the actual finite Wilson random-scan finite path
law is invariant under complete time reversal. -/
theorem finite_lattice_randomScanFinitePathPMF_toReal_reverse
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (path : Fin (n + 1) → L.Configuration) :
    (L.randomScanFinitePathPMF n
        (linearMarkovFinitePathReverse path)).toReal =
      (L.randomScanFinitePathPMF n path).toReal := by
  unfold FiniteLatticeWilsonSystem.randomScanFinitePathPMF
  exact linearMarkovFinitePathPMF_toReal_reverse_of_detailedBalance
    L.gibbsPMF L.randomScanTransitionPMF
      (finite_lattice_randomScanDetailedBalanceReal L) n path

/-- Every finite Wilson random-scan path expectation is invariant under complete
time reversal. -/
theorem finite_lattice_randomScanFinitePathPMF_expectation_reverse
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (H : (Fin (n + 1) → L.Configuration) → ℝ) :
    finitePMFExpectationReal (L.randomScanFinitePathPMF n)
        (H ∘ linearMarkovFinitePathReverse) =
      finitePMFExpectationReal (L.randomScanFinitePathPMF n) H := by
  unfold FiniteLatticeWilsonSystem.randomScanFinitePathPMF
  exact linearMarkovFinitePathPMF_expectation_reverse_of_detailedBalance
    L.gibbsPMF L.randomScanTransitionPMF
      (finite_lattice_randomScanDetailedBalanceReal L) n H

/-- The actual Gibbs-started finite Wilson random-scan path PMF is exactly
invariant under complete time reversal at every finite horizon. -/
theorem finite_lattice_randomScanFinitePathPMF_map_reverse
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    (L.randomScanFinitePathPMF n).map linearMarkovFinitePathReverse =
      L.randomScanFinitePathPMF n := by
  unfold FiniteLatticeWilsonSystem.randomScanFinitePathPMF
  exact linearMarkovFinitePathPMF_map_reverse_of_detailedBalance
    L.gibbsPMF L.randomScanTransitionPMF
      (finite_lattice_randomScanDetailedBalanceReal L) n

end

end MathlibAnalytic
end MGAP4D
