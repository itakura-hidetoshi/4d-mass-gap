import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertShiftSemigroup

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

example (L : FiniteLatticeWilsonSystem) [Nonempty L.Edge] :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup 0 = 1 := by
  simp

example (L : FiniteLatticeWilsonSystem) [Nonempty L.Edge]
    (m n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup (m + n) =
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup m).comp
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n) := by
  exact L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_add m n

example (L : FiniteLatticeWilsonSystem) [Nonempty L.Edge]
    (n : ℕ)
    (x : L.RandomScanTwoSidedIntegerPathOSHilbert) :
    ‖L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n x‖ ≤ ‖x‖ := by
  exact L.norm_randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_le n x

example (L : FiniteLatticeWilsonSystem) [Nonempty L.Edge]
    (n : ℕ)
    (F : linearMarkovPositiveTimeCylinderSubalgebra
      (Ω := L.Configuration)) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n
        (L.randomScanTwoSidedIntegerPathOSHilbertClass F) =
      L.randomScanTwoSidedIntegerPathOSHilbertClass
        (linearMarkovPositiveTimeShiftIterate n F) := by
  simp

end

end MathlibAnalytic
end MGAP4D
