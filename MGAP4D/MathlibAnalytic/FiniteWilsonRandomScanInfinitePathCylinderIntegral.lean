import MGAP4D.MathlibAnalytic.LinearMarkovInfinitePathCylinderIntegral
import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanInfinitePathMeasure
import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanPathCylinderMomentIdentity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- Every finite product cylinder under the actual infinite Wilson random-scan
path measure has exactly the previously constructed random-scan cylinder moment. -/
theorem finite_lattice_randomScanInfinitePathMeasure_cylinder_integral
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (fs : Fin (n + 1) → L.Configuration → ℝ) :
    (∫ path,
        linearMarkovInfinitePathProduct fs path
      ∂L.randomScanInfinitePathMeasure) =
      L.randomScanCylinderMoment (List.ofFn fs) := by
  unfold FiniteLatticeWilsonSystem.randomScanInfinitePathMeasure
  rw [linearMarkovInfinitePathMeasure_cylinder_integral]
  rw [finite_lattice_randomScanTransitionExpectationLinearMap_eq L]
  unfold FiniteLatticeWilsonSystem.randomScanCylinderMoment
    linearMarkovCylinderMoment
  rw [finite_lattice_finitePMFExpectationReal_gibbsPMF]

/-- The all-one finite product cylinder under the actual infinite Wilson path law
has integral one. -/
theorem finite_lattice_randomScanInfinitePathMeasure_cylinder_one
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    (∫ path,
        linearMarkovInfinitePathProduct
          (fun _ : Fin (n + 1) =>
            fun _ : L.Configuration => (1 : ℝ)) path
      ∂L.randomScanInfinitePathMeasure) = 1 := by
  rw [finite_lattice_randomScanInfinitePathMeasure_cylinder_integral]
  exact finite_lattice_randomScanCylinderMoment_replicate_one L (n + 1)

end

end MathlibAnalytic
end MGAP4D
