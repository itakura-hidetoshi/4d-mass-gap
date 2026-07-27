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
    FiniteLatticeWilsonSystem.singleLinkHeatBathProjection,
    finite_lattice_singleLinkHeatBathProjectionLinearMap_apply]

/-- The actual random-scan Wilson heat-bath transition preserves the constant
one observable when the lattice has at least one link. -/
theorem finite_lattice_randomScanHeatBathSweepLinearMap_one
    (L : FiniteLatticeWilsonSystem)
    (hEdge : Nonempty L.Edge) :
    L.randomScanHeatBathSweepLinearMap
        (fun _ : L.Configuration => (1 : ℝ)) =
      fun _ => 1 := by
  classical
  letI : Nonempty L.Edge := hEdge
  have hcardNat : Fintype.card L.Edge ≠ 0 := Fintype.card_ne_zero
  have hcardReal : (Fintype.card L.Edge : ℝ) ≠ 0 := by
    exact_mod_cast hcardNat
  rw [finite_lattice_randomScanHeatBathSweepLinearMap_apply]
  funext A
  rw [finite_lattice_randomScanHeatBathSweep_apply]
  have hone : ∀ e : L.Edge,
      L.singleLinkConditionalExpectation
          (fun _ : L.Configuration => (1 : ℝ)) A e = 1 := by
    intro e
    unfold FiniteLatticeWilsonSystem.singleLinkConditionalExpectation
    simp [finite_pmf_sum_toReal_eq_one]
  simp [hone, hcardReal]

/-- Backward time-zero conditioning of finite cylinders for the actual Wilson
random-scan heat-bath transition. -/
def FiniteLatticeWilsonSystem.randomScanCylinderCondition
    (L : FiniteLatticeWilsonSystem) :
    List (L.Configuration → ℝ) → (L.Configuration → ℝ) :=
  linearMarkovCylinderCondition L.randomScanHeatBathSweepLinearMap

/-- A one-coordinate Wilson cylinder conditions to the original observable. -/
theorem finite_lattice_randomScanCylinderCondition_singleton
    (L : FiniteLatticeWilsonSystem)
    (hEdge : Nonempty L.Edge)
    (f : L.Configuration → ℝ) :
    L.randomScanCylinderCondition [f] = f :=
  linearMarkovCylinderCondition_singleton
    L.randomScanHeatBathSweepLinearMap
    (finite_lattice_randomScanHeatBathSweepLinearMap_one L hEdge)
    f

/-- The actual two-coordinate Wilson cylinder is conditioned by one concrete
random-scan heat-bath step. -/
theorem finite_lattice_randomScanCylinderCondition_pair
    (L : FiniteLatticeWilsonSystem)
    (hEdge : Nonempty L.Edge)
    (f g : L.Configuration → ℝ) :
    L.randomScanCylinderCondition [f, g] =
      fun A => f A * L.randomScanHeatBathSweep g A := by
  rw [FiniteLatticeWilsonSystem.randomScanCylinderCondition,
    linearMarkovCylinderCondition_pair
      L.randomScanHeatBathSweepLinearMap
      (finite_lattice_randomScanHeatBathSweepLinearMap_one L hEdge)]
  funext A
  rw [finite_lattice_randomScanHeatBathSweepLinearMap_apply]

/-- The actual three-coordinate Wilson cylinder has the expected two-step
backward Markov recursion. -/
theorem finite_lattice_randomScanCylinderCondition_triple
    (L : FiniteLatticeWilsonSystem)
    (hEdge : Nonempty L.Edge)
    (f g h : L.Configuration → ℝ) :
    L.randomScanCylinderCondition [f, g, h] =
      fun A => f A *
        L.randomScanHeatBathSweep
          (fun B => g B * L.randomScanHeatBathSweep h B) A := by
  rw [FiniteLatticeWilsonSystem.randomScanCylinderCondition,
    linearMarkovCylinderCondition_triple
      L.randomScanHeatBathSweepLinearMap
      (finite_lattice_randomScanHeatBathSweepLinearMap_one L hEdge)]
  funext A
  rw [finite_lattice_randomScanHeatBathSweepLinearMap_apply]
  congr 2
  funext B
  rw [finite_lattice_randomScanHeatBathSweepLinearMap_apply]

/-- Every all-one finite Wilson random-scan cylinder is normalized when the
lattice has at least one link. -/
theorem finite_lattice_randomScanCylinderCondition_replicate_one
    (L : FiniteLatticeWilsonSystem)
    (hEdge : Nonempty L.Edge)
    (n : ℕ) :
    L.randomScanCylinderCondition
        (List.replicate n (fun _ : L.Configuration => (1 : ℝ))) =
      fun _ => 1 :=
  linearMarkovCylinderCondition_replicate_one
    L.randomScanHeatBathSweepLinearMap
    (finite_lattice_randomScanHeatBathSweepLinearMap_one L hEdge)
    n

end

end MathlibAnalytic
end MGAP4D
