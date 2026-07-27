import MGAP4D.MathlibAnalytic.LinearMarkovFinitePathCylinderExpectation
import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanFinitePathPMF
import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanCylinderMoment
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- The generic transition-PMF expectation linear map for the actual finite
Wilson random-scan kernel is exactly the previously constructed random-scan
heat-bath sweep linear map. -/
theorem finite_lattice_randomScanTransitionExpectationLinearMap_eq
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    finitePMFTransitionExpectationLinearMap L.randomScanTransitionPMF =
      L.randomScanHeatBathSweepLinearMap := by
  ext f A
  rw [finitePMFTransitionExpectationLinearMap_apply,
    finite_lattice_randomScanHeatBathSweepLinearMap_apply]
  exact finite_lattice_randomScanTransitionPMF_expectation L A f

/-- For every finite tuple of actual finite Wilson observables, expectation of
their coordinatewise product under the honest Gibbs-started random-scan path PMF
is exactly the existing random-scan cylinder moment. -/
theorem finite_lattice_randomScanFinitePathPMF_cylinderProduct_expectation
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (fs : Fin (n + 1) → L.Configuration → ℝ) :
    finitePMFExpectationReal
        (L.randomScanFinitePathPMF n)
        (fun path => ∏ i : Fin (n + 1), fs i (path i)) =
      L.randomScanCylinderMoment (List.ofFn fs) := by
  unfold FiniteLatticeWilsonSystem.randomScanFinitePathPMF
  rw [linearMarkovFinitePathPMF_cylinderProduct_expectation]
  unfold FiniteLatticeWilsonSystem.randomScanCylinderMoment
  congr 1
  · funext f
    exact finite_lattice_finitePMFExpectationReal_gibbsPMF L f
  · exact finite_lattice_randomScanTransitionExpectationLinearMap_eq L

/-- The terminal-separated form of the actual finite Wilson path-PMF/cylinder
moment identity. -/
theorem finite_lattice_randomScanFinitePathPMF_terminalCylinder_expectation
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (fs : Fin n → L.Configuration → ℝ)
    (h : L.Configuration → ℝ) :
    finitePMFExpectationReal
        (L.randomScanFinitePathPMF n)
        (linearMarkovFinitePathCylinderProduct n fs h) =
      L.randomScanCylinderMoment (List.ofFn fs ++ [h]) := by
  unfold FiniteLatticeWilsonSystem.randomScanFinitePathPMF
  rw [linearMarkovFinitePathPMF_terminalCylinder_expectation]
  unfold FiniteLatticeWilsonSystem.randomScanCylinderMoment
  congr 1
  · funext f
    exact finite_lattice_finitePMFExpectationReal_gibbsPMF L f
  · exact finite_lattice_randomScanTransitionExpectationLinearMap_eq L

end

end MathlibAnalytic
end MGAP4D
