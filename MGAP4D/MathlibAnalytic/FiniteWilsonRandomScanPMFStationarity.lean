import MGAP4D.MathlibAnalytic.LinearMarkovFiniteDimensionalPMFStationarity
import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTransitionExpectation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- One application of the actual finite Wilson random-scan transition preserves
expectation under the finite Gibbs PMF, expressed entirely in PMF expectation
language. -/
theorem finite_lattice_randomScanTransitionPMF_gibbs_expectation_stationary
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (f : L.Configuration → ℝ) :
    finitePMFExpectationReal L.gibbsPMF
        (fun A =>
          finitePMFExpectationReal (L.randomScanTransitionPMF A) f) =
      finitePMFExpectationReal L.gibbsPMF f := by
  simp_rw [finite_lattice_randomScanTransitionPMF_expectation]
  simp only [finite_lattice_finitePMFExpectationReal_gibbsPMF]
  exact finite_lattice_gibbsExpectationReal_randomScanHeatBathSweep L f

/-- The terminal marginal of the Gibbs-started one-step finite Wilson
random-scan path PMF is exactly the finite Gibbs PMF. -/
theorem finite_lattice_randomScanPairPMF_map_snd
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    L.randomScanPairPMF.map Prod.snd = L.gibbsPMF := by
  unfold FiniteLatticeWilsonSystem.randomScanPairPMF
  exact
    linearMarkovPairPMF_map_snd_of_expectation_stationary
      L.gibbsPMF L.randomScanTransitionPMF
      (finite_lattice_randomScanTransitionPMF_gibbs_expectation_stationary L)

/-- The time-zero marginal of the Gibbs-started two-step finite Wilson path PMF
is the finite Gibbs PMF. -/
theorem finite_lattice_randomScanTriplePMF_map_first
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    L.randomScanTriplePMF.map (fun xyz => xyz.1) =
      L.gibbsPMF := by
  calc
    L.randomScanTriplePMF.map (fun xyz => xyz.1) =
        (L.randomScanTriplePMF.map linearMarkovTripleDropLast).map
          Prod.fst := by
            rw [PMF.map_comp]
            rfl
    _ = L.randomScanPairPMF.map Prod.fst := by
      rw [finite_lattice_randomScanTriplePMF_map_dropLast]
    _ = L.gibbsPMF :=
      finite_lattice_randomScanPairPMF_map_fst L

/-- The time-one marginal of the Gibbs-started two-step finite Wilson path PMF
is the finite Gibbs PMF. -/
theorem finite_lattice_randomScanTriplePMF_map_second
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    L.randomScanTriplePMF.map (fun xyz => xyz.2.1) =
      L.gibbsPMF := by
  calc
    L.randomScanTriplePMF.map (fun xyz => xyz.2.1) =
        (L.randomScanTriplePMF.map linearMarkovTripleDropLast).map
          Prod.snd := by
            rw [PMF.map_comp]
            rfl
    _ = L.randomScanPairPMF.map Prod.snd := by
      rw [finite_lattice_randomScanTriplePMF_map_dropLast]
    _ = L.gibbsPMF :=
      finite_lattice_randomScanPairPMF_map_snd L

/-- The terminal marginal of the Gibbs-started two-step finite Wilson
random-scan path PMF is exactly the finite Gibbs PMF. -/
theorem finite_lattice_randomScanTriplePMF_map_third
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    L.randomScanTriplePMF.map (fun xyz => xyz.2.2) =
      L.gibbsPMF := by
  unfold FiniteLatticeWilsonSystem.randomScanTriplePMF
  exact
    linearMarkovTriplePMF_map_third_of_expectation_stationary
      L.gibbsPMF L.randomScanTransitionPMF
      (finite_lattice_randomScanTransitionPMF_gibbs_expectation_stationary L)

end

end MathlibAnalytic
end MGAP4D
