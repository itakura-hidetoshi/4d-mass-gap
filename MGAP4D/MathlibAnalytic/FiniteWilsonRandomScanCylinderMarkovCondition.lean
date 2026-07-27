import MGAP4D.MathlibAnalytic.LinearMarkovCylinderCondition
import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonRandomScanHeatBathSweep
import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonSingleLinkHeatBathLinearProjection
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped BigOperators

/-- The concrete random-scan heat-bath sweep bundled as a real-linear
transition operator on finite Wilson observables. -/
noncomputable def FiniteLatticeWilsonSystem.randomScanHeatBathSweepLinearMap
    (L : FiniteLatticeWilsonSystem) :
    (L.Configuration → ℝ) →ₗ[ℝ] (L.Configuration → ℝ) := by
  classical
  exact (Fintype.card L.Edge : ℝ)⁻¹ •
    ∑ e : L.Edge, L.singleLinkHeatBathProjectionLinearMap e

@[simp] theorem finite_lattice_randomScanHeatBathSweepLinearMap_apply
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    L.randomScanHeatBathSweepLinearMap f =
      L.randomScanHeatBathSweep f := by
  classical
  funext A
  simp [FiniteLatticeWilsonSystem.randomScanHeatBathSweepLinearMap,
    FiniteLatticeWilsonSystem.randomScanHeatBathSweep,
    FiniteLatticeWilsonSystem.singleLinkHeatBathOperator,
    finite_lattice_singleLinkHeatBathProjectionLinearMap_apply]

/-- The actual random-scan Wilson heat-bath transition preserves the constant
one observable. -/
theorem finite_lattice_randomScanHeatBathSweepLinearMap_one
    (L : FiniteLatticeWilsonSystem) :
    L.randomScanHeatBathSweepLinearMap
        (fun _ : L.Configuration => (1 : ℝ)) =
      fun _ => 1 := by
  classical
  rw [finite_lattice_randomScanHeatBathSweepLinearMap_apply]
  funext A
  rw [finite_lattice_randomScanHeatBathSweep_apply]
  simp [finite_lattice_singleLinkHeatBathProjection_one]

/-- Backward time-zero conditioning of finite cylinders for the actual Wilson
random-scan heat-bath transition. -/
def FiniteLatticeWilsonSystem.randomScanCylinderCondition
    (L : FiniteLatticeWilsonSystem) :
    List (L.Configuration → ℝ) → (L.Configuration → ℝ) :=
  linearMarkovCylinderCondition L.randomScanHeatBathSweepLinearMap

/-- A one-coordinate Wilson cylinder conditions to the original observable. -/
theorem finite_lattice_randomScanCylinderCondition_singleton
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    L.randomScanCylinderCondition [f] = f :=
  linearMarkovCylinderCondition_singleton
    L.randomScanHeatBathSweepLinearMap
    (finite_lattice_randomScanHeatBathSweepLinearMap_one L)
    f

/-- The actual two-coordinate Wilson cylinder is conditioned by one concrete
random-scan heat-bath step. -/
theorem finite_lattice_randomScanCylinderCondition_pair
    (L : FiniteLatticeWilsonSystem)
    (f g : L.Configuration → ℝ) :
    L.randomScanCylinderCondition [f, g] =
      fun A => f A * L.randomScanHeatBathSweep g A := by
  rw [FiniteLatticeWilsonSystem.randomScanCylinderCondition,
    linearMarkovCylinderCondition_pair
      L.randomScanHeatBathSweepLinearMap
      (finite_lattice_randomScanHeatBathSweepLinearMap_one L)]
  funext A
  rw [finite_lattice_randomScanHeatBathSweepLinearMap_apply]

/-- The actual three-coordinate Wilson cylinder has the expected two-step
backward Markov recursion. -/
theorem finite_lattice_randomScanCylinderCondition_triple
    (L : FiniteLatticeWilsonSystem)
    (f g h : L.Configuration → ℝ) :
    L.randomScanCylinderCondition [f, g, h] =
      fun A => f A *
        L.randomScanHeatBathSweep
          (fun B => g B * L.randomScanHeatBathSweep h B) A := by
  rw [FiniteLatticeWilsonSystem.randomScanCylinderCondition,
    linearMarkovCylinderCondition_triple
      L.randomScanHeatBathSweepLinearMap
      (finite_lattice_randomScanHeatBathSweepLinearMap_one L)]
  funext A
  rw [finite_lattice_randomScanHeatBathSweepLinearMap_apply]
  congr 2
  funext B
  rw [finite_lattice_randomScanHeatBathSweepLinearMap_apply]

/-- Every all-one finite Wilson random-scan cylinder is normalized. -/
theorem finite_lattice_randomScanCylinderCondition_replicate_one
    (L : FiniteLatticeWilsonSystem)
    (n : ℕ) :
    L.randomScanCylinderCondition
        (List.replicate n (fun _ : L.Configuration => (1 : ℝ))) =
      fun _ => 1 :=
  linearMarkovCylinderCondition_replicate_one
    L.randomScanHeatBathSweepLinearMap
    (finite_lattice_randomScanHeatBathSweepLinearMap_one L)
    n

end

end MathlibAnalytic
end MGAP4D
