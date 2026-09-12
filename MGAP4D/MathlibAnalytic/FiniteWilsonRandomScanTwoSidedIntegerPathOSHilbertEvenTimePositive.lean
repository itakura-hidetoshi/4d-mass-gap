import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertSymmetricContractionSemigroup
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertEvenTimePositive

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- At every even natural time, the actual finite Wilson temporal OS quadratic
form is the squared norm of the half-time translate. -/
theorem FiniteLatticeWilsonSystem.inner_randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_add_self_eq
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (x : L.RandomScanTwoSidedIntegerPathOSHilbert) :
    inner ℝ
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup (n + n) x) x =
      inner ℝ
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n x)
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n x) :=
  LinearMarkovTwoSidedIntegerPathOSPreHilbertData.inner_hilbertShiftSemigroup_add_self_eq
    L.randomScanTwoSidedIntegerPathOSPreHilbertData n x

/-- Every even-time member of the actual finite Wilson temporal OS semigroup
has nonnegative quadratic form. -/
theorem FiniteLatticeWilsonSystem.inner_randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_add_self_nonneg
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (x : L.RandomScanTwoSidedIntegerPathOSHilbert) :
    0 ≤ inner ℝ
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup (n + n) x) x :=
  LinearMarkovTwoSidedIntegerPathOSPreHilbertData.inner_hilbertShiftSemigroup_add_self_nonneg
    L.randomScanTwoSidedIntegerPathOSPreHilbertData n x

end

end MathlibAnalytic
end MGAP4D
