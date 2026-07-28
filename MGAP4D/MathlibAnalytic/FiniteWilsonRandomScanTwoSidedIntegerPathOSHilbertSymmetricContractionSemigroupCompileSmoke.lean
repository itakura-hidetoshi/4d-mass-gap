import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertSymmetricContractionSemigroup

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

example (L : FiniteLatticeWilsonSystem) [Nonempty L.Edge]
    (m n : ℕ) :
    (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup m).comp
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n) =
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n).comp
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup m) :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_comp_comm m n

example (L : FiniteLatticeWilsonSystem) [Nonempty L.Edge]
    (n : ℕ)
    (x y : L.RandomScanTwoSidedIntegerPathOSHilbert) :
    inner ℝ (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n x) y =
      inner ℝ x
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n y) :=
  L.inner_randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_left_eq_right n x y

example (L : FiniteLatticeWilsonSystem) [Nonempty L.Edge]
    (n : ℕ)
    (x : L.RandomScanTwoSidedIntegerPathOSHilbert) :
    ‖L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n x‖ ≤ ‖x‖ :=
  L.norm_randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_le n x

end

end MathlibAnalytic
end MGAP4D
