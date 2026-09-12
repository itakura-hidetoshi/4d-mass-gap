import MGAP4D.MathlibAnalytic.LinearMarkovFinitePathPrefixConsistency
import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanFinitePathPMF
import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanCylinderMoment
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The actual finite Wilson random-scan path PMFs are projectively consistent
between arbitrary finite prefix horizons. -/
theorem finite_lattice_randomScanFinitePathPMF_map_prefix
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (m k : ℕ) :
    (L.randomScanFinitePathPMF (m + k)).map
        (linearMarkovFinitePathPrefix m k) =
      L.randomScanFinitePathPMF m := by
  unfold FiniteLatticeWilsonSystem.randomScanFinitePathPMF
  exact
    linearMarkovFinitePathPMF_map_prefix
      L.gibbsPMF L.randomScanTransitionPMF m k

/-- Appending any finite number of unobserved terminal time coordinates leaves
the actual finite Wilson random-scan cylinder moment unchanged. -/
theorem finite_lattice_randomScanCylinderMoment_append_replicate_one
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (fs : List (L.Configuration → ℝ))
    (k : ℕ) :
    L.randomScanCylinderMoment
        (fs ++ List.replicate k
          (fun _ : L.Configuration => (1 : ℝ))) =
      L.randomScanCylinderMoment fs := by
  unfold FiniteLatticeWilsonSystem.randomScanCylinderMoment
  exact
    linearMarkovCylinderMoment_append_replicate_one
      L.gibbsExpectationReal
      L.randomScanHeatBathSweepLinearMap
      (finite_lattice_randomScanHeatBathSweepLinearMap_one L inferInstance)
      fs k

end

end MathlibAnalytic
end MGAP4D
