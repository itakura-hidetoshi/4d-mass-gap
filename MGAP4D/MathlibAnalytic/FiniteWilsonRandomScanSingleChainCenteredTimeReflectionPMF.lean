import MGAP4D.MathlibAnalytic.LinearMarkovSingleChainCenteredTimeReflectionPMF
import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanCenteredTimeReflectionPMF
import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanFinitePathReversal
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The actual finite Wilson centered path law obtained from one chronological
Gibbs-stationary random-scan chain: a past segment ending at time zero followed
by the positive-time continuation from the same terminal configuration. -/
abbrev FiniteLatticeWilsonSystem.randomScanSingleChainCenteredFinitePathPMF
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    PMF (L.RandomScanCenteredFinitePath n) :=
  linearMarkovSingleChainCenteredFinitePathPMF
    L.gibbsPMF L.randomScanTransitionPMF n

/-- The actual doubled-future centered PMF is exactly the past/boundary/future
law of one reversible finite Wilson random-scan chain. -/
theorem finite_lattice_randomScanSingleChainCenteredFinitePathPMF_eq_centered
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    L.randomScanSingleChainCenteredFinitePathPMF n =
      L.randomScanCenteredFinitePathPMF n :=
  linearMarkovSingleChainCenteredFinitePathPMF_eq_centered_of_detailedBalance
    L.gibbsPMF L.randomScanTransitionPMF
      (finite_lattice_randomScanDetailedBalanceReal L) n

/-- Complete time reflection preserves the actual single-chain centered finite
Wilson path law. -/
theorem finite_lattice_randomScanSingleChainCenteredFinitePathPMF_map_reflection
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    (L.randomScanSingleChainCenteredFinitePathPMF n).map
        L.randomScanCenteredFinitePathReflection =
      L.randomScanSingleChainCenteredFinitePathPMF n :=
  linearMarkovSingleChainCenteredFinitePathPMF_map_reflection
    L.gibbsPMF L.randomScanTransitionPMF
      (finite_lattice_randomScanDetailedBalanceReal L) n

/-- The actual temporal OS bilinear form is a reflected-product expectation
under the past/boundary/future decomposition of one reversible random-scan
chain. -/
theorem finite_lattice_randomScanSingleChainCenteredFinitePathPMF_reflectedProduct_expectation_eq_OSForm
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (F G : LinearMarkovPositiveTimeFuturePath L.Configuration n → ℝ) :
    finitePMFExpectationReal
        (L.randomScanSingleChainCenteredFinitePathPMF n)
        (fun path =>
          linearMarkovCenteredFinitePathPositiveLift F
              (L.randomScanCenteredFinitePathReflection path) *
            linearMarkovCenteredFinitePathPositiveLift G path) =
      L.randomScanPositiveTimeOSForm n F G :=
  linearMarkovSingleChainCenteredFinitePathPMF_reflectedProduct_expectation_eq_OSForm
    L.gibbsPMF L.randomScanTransitionPMF
      (finite_lattice_randomScanDetailedBalanceReal L) n F G

/-- The reflected square under the actual single-chain centered Wilson law is
nonnegative. -/
theorem finite_lattice_randomScanSingleChainCenteredFinitePathPMF_reflectedSquare_nonneg
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (F : LinearMarkovPositiveTimeFuturePath L.Configuration n → ℝ) :
    0 ≤ finitePMFExpectationReal
        (L.randomScanSingleChainCenteredFinitePathPMF n)
        (fun path =>
          linearMarkovCenteredFinitePathPositiveLift F
              (L.randomScanCenteredFinitePathReflection path) *
            linearMarkovCenteredFinitePathPositiveLift F path) := by
  rw [finite_lattice_randomScanSingleChainCenteredFinitePathPMF_reflectedProduct_expectation_eq_OSForm]
  exact finite_lattice_randomScanPositiveTimeOSForm_nonneg L n F

end

end MathlibAnalytic
end MGAP4D
