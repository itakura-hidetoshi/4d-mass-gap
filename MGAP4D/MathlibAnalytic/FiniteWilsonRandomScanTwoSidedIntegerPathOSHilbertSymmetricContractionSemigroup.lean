import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertShiftSemigroup
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertSymmetricContractionSemigroup

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The actual finite Wilson discrete temporal OS semigroup members commute. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_comp_comm
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (m n : ℕ) :
    (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup m).comp
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n) =
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n).comp
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup m) :=
  LinearMarkovTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroup_comp_comm
    L.randomScanTwoSidedIntegerPathOSPreHilbertData m n

/-- Every actual finite Wilson discrete temporal OS semigroup member is
symmetric on the completed real Hilbert space. -/
theorem FiniteLatticeWilsonSystem.inner_randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_left_eq_right
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (x y : L.RandomScanTwoSidedIntegerPathOSHilbert) :
    inner ℝ (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n x) y =
      inner ℝ x
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n y) :=
  LinearMarkovTwoSidedIntegerPathOSPreHilbertData.inner_hilbertShiftSemigroup_left_eq_right
    L.randomScanTwoSidedIntegerPathOSPreHilbertData n x y

end

end MathlibAnalytic
end MGAP4D
