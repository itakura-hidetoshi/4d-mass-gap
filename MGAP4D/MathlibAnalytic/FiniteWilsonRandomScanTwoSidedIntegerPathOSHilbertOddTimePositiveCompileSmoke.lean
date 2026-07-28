import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertOddTimePositive

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (x : L.RandomScanTwoSidedIntegerPathOSHilbert) :
    0 ≤ inner ℝ (L.randomScanTwoSidedIntegerPathOSHilbertShift x) x :=
  L.inner_randomScanTwoSidedIntegerPathOSHilbertShift_self_nonneg x

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (x : L.RandomScanTwoSidedIntegerPathOSHilbert) :
    0 ≤ inner ℝ
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup
        (n + n + 1) x) x :=
  L.inner_randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_add_self_add_one_nonneg
    n x

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (x : L.RandomScanTwoSidedIntegerPathOSHilbert) :
    0 ≤ inner ℝ
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup
        (n + n) x) x :=
  L.inner_randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_add_self_nonneg
    n x

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (x : L.RandomScanTwoSidedIntegerPathOSHilbert) :
    ‖L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n x‖ ≤ ‖x‖ :=
  L.norm_randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_le n x

end

end MathlibAnalytic
end MGAP4D
