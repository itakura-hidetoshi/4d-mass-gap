import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathMeasure
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathReflectionInvariance

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The actual finite Wilson Gibbs-stationary random-scan two-sided path law is
invariant under global integer-time reflection `t ↦ -t`. -/
theorem finite_lattice_randomScanTwoSidedIntegerPathMeasure_map_reflection
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    L.randomScanTwoSidedIntegerPathMeasure.map
        linearMarkovIntegerPathReflection =
      L.randomScanTwoSidedIntegerPathMeasure := by
  unfold FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathMeasure
  exact linearMarkovTwoSidedIntegerPathMeasure_map_reflection
    L.gibbsPMF L.randomScanTransitionPMF
      (finite_lattice_randomScanDetailedBalanceReal L)

end

end MathlibAnalytic
end MGAP4D
