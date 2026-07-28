import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertShift

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

example (L : FiniteLatticeWilsonSystem) [Nonempty L.Edge] :
    L.RandomScanTwoSidedIntegerPathOSHilbert →L[ℝ]
      L.RandomScanTwoSidedIntegerPathOSHilbert :=
  L.randomScanTwoSidedIntegerPathOSHilbertShift

example (L : FiniteLatticeWilsonSystem) [Nonempty L.Edge]
    (x : L.RandomScanTwoSidedIntegerPathOSHilbert) :
    ‖L.randomScanTwoSidedIntegerPathOSHilbertShift x‖ ≤ ‖x‖ :=
  L.norm_randomScanTwoSidedIntegerPathOSHilbertShift_le x

example (L : FiniteLatticeWilsonSystem) [Nonempty L.Edge]
    (x y : L.RandomScanTwoSidedIntegerPathOSHilbert) :
    inner ℝ (L.randomScanTwoSidedIntegerPathOSHilbertShift x) y =
      inner ℝ x (L.randomScanTwoSidedIntegerPathOSHilbertShift y) :=
  L.inner_randomScanTwoSidedIntegerPathOSHilbertShift_left_eq_right x y

end

end MathlibAnalytic
end MGAP4D
