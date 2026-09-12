import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertComplexContinuousSpectrumInterval

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped ComplexOrder

variable (L : FiniteLatticeWilsonSystem) [Nonempty L.Edge]

example (n : ℕ) :
    ‖L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n‖ ≤ 1 :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap_opNorm_le_one n

example (n : ℕ) :
    spectrum ℂ
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n) ⊆
      Set.Icc (0 : ℂ) 1 :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap_spectrum_subset_Icc n

example (n : ℕ) {c : ℂ}
    (hc : c ∈ spectrum ℂ
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n)) :
    c ∈ Set.Icc (0 : ℂ) 1 :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap_spectrum_mem_Icc n hc

example (n : ℕ) {r : ℝ}
    (hr : r ∈ spectrum ℝ
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n)) :
    0 ≤ r :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap_real_spectrum_nonneg n hr

example (n : ℕ) {r : ℝ}
    (hr : r ∈ spectrum ℝ
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n)) :
    r ≤ 1 :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap_real_spectrum_le_one n hr

example :
    ‖L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap‖ ≤ 1 :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap_opNorm_le_one

example :
    spectrum ℂ
        L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap ⊆
      Set.Icc (0 : ℂ) 1 :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap_spectrum_subset_Icc

example {c : ℂ}
    (hc : c ∈ spectrum ℂ
      L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap) :
    c ∈ Set.Icc (0 : ℂ) 1 :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap_spectrum_mem_Icc hc

end

end MathlibAnalytic
end MGAP4D
