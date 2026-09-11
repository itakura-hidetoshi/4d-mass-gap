import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertSpectralRadius

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped ENNReal NNReal

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    spectralRadius ℝ
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n) =
      (‖L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n‖₊ : ℝ≥0∞) :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_spectralRadius_eq_nnnorm n

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    ‖L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n‖₊ ≤ 1 :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_nnnorm_le_one n

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    spectralRadius ℝ
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n) ≤ 1 :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_spectralRadius_le_one n

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    (spectralRadius ℝ
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n)).toReal =
      ‖L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n‖ :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_spectralRadius_toReal_eq_norm n

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    spectralRadius ℝ
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n) ∈
        Set.Icc (0 : ℝ≥0∞) 1 :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_spectralRadius_mem_Icc n

end

end MathlibAnalytic
end MGAP4D
