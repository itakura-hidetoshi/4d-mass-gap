import MGAP4D.MathlibAnalytic.LinearMarkovFiniteDimensionalPMF
import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonSingleLinkHeatBath
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The actual finite Wilson random-scan transition law from one configuration.
First choose a lattice link uniformly, then resample that link from its exact
Wilson Gibbs conditional PMF. -/
def FiniteLatticeWilsonSystem.randomScanTransitionPMF
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (A : L.Configuration) : PMF L.Configuration :=
  (PMF.uniformOfFintype L.Edge).bind fun e =>
    (L.singleLinkConditionalPMF A e).map fun g =>
      L.replaceLink A e g

/-- The actual one-step finite Wilson path law, started in the finite Gibbs PMF. -/
def FiniteLatticeWilsonSystem.randomScanPairPMF
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] : PMF (L.Configuration × L.Configuration) :=
  linearMarkovPairPMF L.gibbsPMF L.randomScanTransitionPMF

/-- The actual two-step finite Wilson path law, started in the finite Gibbs PMF. -/
def FiniteLatticeWilsonSystem.randomScanTriplePMF
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    PMF (L.Configuration × L.Configuration × L.Configuration) :=
  linearMarkovTriplePMF L.gibbsPMF L.randomScanTransitionPMF

/-- Every actual finite Wilson random-scan transition probability is
nonnegative. -/
theorem finite_lattice_randomScanTransitionPMF_nonneg
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (A B : L.Configuration) :
    0 ≤ L.randomScanTransitionPMF A B :=
  bot_le

/-- Every point probability of the actual one-step finite Wilson path law is
nonnegative. -/
theorem finite_lattice_randomScanPairPMF_nonneg
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (AB : L.Configuration × L.Configuration) :
    0 ≤ L.randomScanPairPMF AB :=
  bot_le

/-- The time-zero marginal of the actual one-step random-scan path law is the
finite Wilson Gibbs PMF. -/
theorem finite_lattice_randomScanPairPMF_map_fst
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    L.randomScanPairPMF.map Prod.fst = L.gibbsPMF := by
  unfold FiniteLatticeWilsonSystem.randomScanPairPMF
  exact
    linearMarkovPairPMF_map_fst
      L.gibbsPMF L.randomScanTransitionPMF

/-- Deleting the unobserved terminal coordinate from the actual two-step finite
Wilson path law recovers the one-step path law. -/
theorem finite_lattice_randomScanTriplePMF_map_dropLast
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    L.randomScanTriplePMF.map linearMarkovTripleDropLast =
      L.randomScanPairPMF := by
  unfold FiniteLatticeWilsonSystem.randomScanTriplePMF
    FiniteLatticeWilsonSystem.randomScanPairPMF
  exact
    linearMarkovTriplePMF_map_dropLast
      L.gibbsPMF L.randomScanTransitionPMF

/-- Every point probability of the actual two-step finite Wilson path law is
nonnegative. -/
theorem finite_lattice_randomScanTriplePMF_nonneg
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (ABC : L.Configuration × L.Configuration × L.Configuration) :
    0 ≤ L.randomScanTriplePMF ABC :=
  bot_le

end

end MathlibAnalytic
end MGAP4D
