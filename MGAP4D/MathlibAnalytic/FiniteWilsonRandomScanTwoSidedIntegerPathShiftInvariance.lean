import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathMeasure
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathShiftInvariance

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The actual finite Wilson Gibbs-stationary random-scan two-sided path law is
invariant under every integer-time translation. -/
theorem finite_lattice_randomScanTwoSidedIntegerPathMeasure_map_shift
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (k : ℤ) :
    L.randomScanTwoSidedIntegerPathMeasure.map
        (linearMarkovIntegerPathShift k) =
      L.randomScanTwoSidedIntegerPathMeasure := by
  unfold FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathMeasure
  exact linearMarkovTwoSidedIntegerPathMeasure_map_shift
    L.gibbsPMF L.randomScanTransitionPMF
      (finite_lattice_randomScanDetailedBalanceReal L) k

/-- Natural-time translations preserve the actual finite Wilson two-sided path
law. -/
theorem finite_lattice_randomScanTwoSidedIntegerPathMeasure_map_natShift
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (d : ℕ) :
    L.randomScanTwoSidedIntegerPathMeasure.map
        (linearMarkovIntegerPathShift ((d : ℕ) : ℤ)) =
      L.randomScanTwoSidedIntegerPathMeasure := by
  exact finite_lattice_randomScanTwoSidedIntegerPathMeasure_map_shift
    L ((d : ℕ) : ℤ)

/-- Nonpositive integer-time translations preserve the actual finite Wilson
path law as well. -/
theorem finite_lattice_randomScanTwoSidedIntegerPathMeasure_map_negNatShift
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (d : ℕ) :
    L.randomScanTwoSidedIntegerPathMeasure.map
        (linearMarkovIntegerPathShift (-((d : ℕ) : ℤ))) =
      L.randomScanTwoSidedIntegerPathMeasure := by
  exact finite_lattice_randomScanTwoSidedIntegerPathMeasure_map_shift
    L (-((d : ℕ) : ℤ))

end

end MathlibAnalytic
end MGAP4D
