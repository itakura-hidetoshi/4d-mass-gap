import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertEvenTimePositive

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (x : L.RandomScanTwoSidedIntegerPathOSHilbert) :
    inner ℝ
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup (n + n) x) x =
      inner ℝ
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n x)
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n x) :=
  L.inner_randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_add_self_eq n x

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (x : L.RandomScanTwoSidedIntegerPathOSHilbert) :
    0 ≤ inner ℝ
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup (n + n) x) x :=
  L.inner_randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_add_self_nonneg n x

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
