import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertPositiveSelfAdjoint

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (x : L.RandomScanTwoSidedIntegerPathOSHilbert) :
    0 ≤ inner ℝ
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n x) x :=
  L.inner_randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_self_nonneg n x

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n).IsPositive :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_isPositive n

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    0 ≤ L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_nonneg n

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    IsSelfAdjoint
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n) :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_isSelfAdjoint n

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    ContinuousLinearMap.adjoint
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n) =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_adjoint_eq n

end

end MathlibAnalytic
end MGAP4D
