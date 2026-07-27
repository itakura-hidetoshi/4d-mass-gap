import MGAP4D.MathlibAnalytic.LinearMarkovCylinderMoment
import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanCylinderMarkovCondition
import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonGibbsRealVariance
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The finite Wilson Gibbs law is normalized as a real expectation functional. -/
theorem finite_lattice_gibbsExpectationReal_one
    (L : FiniteLatticeWilsonSystem) :
    L.gibbsExpectationReal (fun _ : L.Configuration => (1 : ℝ)) = 1 := by
  classical
  unfold FiniteLatticeWilsonSystem.gibbsExpectationReal
  simp only [mul_one, FiniteLatticeWilsonSystem.gibbsProbabilityReal]
  exact finite_pmf_sum_toReal_eq_one L.gibbsPMF

/-- Finite-cylinder moments for the actual random-scan Wilson heat-bath chain,
started in the finite Gibbs law. -/
def FiniteLatticeWilsonSystem.randomScanCylinderMoment
    (L : FiniteLatticeWilsonSystem)
    (fs : List (L.Configuration → ℝ)) : ℝ :=
  linearMarkovCylinderMoment
    L.gibbsExpectationReal
    L.randomScanHeatBathSweepLinearMap
    fs

/-- The empty finite Wilson random-scan cylinder has moment one. -/
theorem finite_lattice_randomScanCylinderMoment_nil
    (L : FiniteLatticeWilsonSystem) :
    L.randomScanCylinderMoment [] = 1 :=
  linearMarkovCylinderMoment_nil
    L.gibbsExpectationReal
    L.randomScanHeatBathSweepLinearMap
    (finite_lattice_gibbsExpectationReal_one L)

/-- A one-coordinate finite Wilson cylinder recovers Gibbs expectation. -/
theorem finite_lattice_randomScanCylinderMoment_singleton
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (f : L.Configuration → ℝ) :
    L.randomScanCylinderMoment [f] = L.gibbsExpectationReal f :=
  linearMarkovCylinderMoment_singleton
    L.gibbsExpectationReal
    L.randomScanHeatBathSweepLinearMap
    (finite_lattice_randomScanHeatBathSweepLinearMap_one L)
    f

/-- A two-coordinate finite Wilson cylinder is the Gibbs expectation of the
one-step random-scan Markov product. -/
theorem finite_lattice_randomScanCylinderMoment_pair
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (f g : L.Configuration → ℝ) :
    L.randomScanCylinderMoment [f, g] =
      L.gibbsExpectationReal
        (fun A => f A * L.randomScanHeatBathSweep g A) := by
  rw [FiniteLatticeWilsonSystem.randomScanCylinderMoment,
    linearMarkovCylinderMoment_pair
      L.gibbsExpectationReal
      L.randomScanHeatBathSweepLinearMap
      (finite_lattice_randomScanHeatBathSweepLinearMap_one L)]
  congr 1
  funext A
  rw [finite_lattice_randomScanHeatBathSweepLinearMap_apply]

/-- The actual finite Wilson cylinder moments are projectively consistent when an
unobserved terminal coordinate is appended. -/
theorem finite_lattice_randomScanCylinderMoment_append_one
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (fs : List (L.Configuration → ℝ)) :
    L.randomScanCylinderMoment
        (fs ++ [fun _ : L.Configuration => (1 : ℝ)]) =
      L.randomScanCylinderMoment fs :=
  linearMarkovCylinderMoment_append_one
    L.gibbsExpectationReal
    L.randomScanHeatBathSweepLinearMap
    (finite_lattice_randomScanHeatBathSweepLinearMap_one L)
    fs

/-- Every all-one finite Wilson cylinder has normalized moment one. -/
theorem finite_lattice_randomScanCylinderMoment_replicate_one
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    L.randomScanCylinderMoment
        (List.replicate n (fun _ : L.Configuration => (1 : ℝ))) = 1 := by
  rw [FiniteLatticeWilsonSystem.randomScanCylinderMoment,
    linearMarkovCylinderMoment]
  rw [linearMarkovCylinderCondition_replicate_one
    L.randomScanHeatBathSweepLinearMap
    (finite_lattice_randomScanHeatBathSweepLinearMap_one L)]
  exact finite_lattice_gibbsExpectationReal_one L

end

end MathlibAnalytic
end MGAP4D
