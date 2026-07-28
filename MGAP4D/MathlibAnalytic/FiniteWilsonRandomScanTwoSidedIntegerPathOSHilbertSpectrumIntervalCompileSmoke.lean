import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertSpectrumInterval

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    ‖L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n‖ ≤ 1 :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_opNorm_le_one n

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    spectrum ℝ (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n) ⊆
      Set.Icc (0 : ℝ) 1 :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_spectrum_subset_Icc n

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    {c : ℝ}
    (hc : c ∈ spectrum ℝ
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n)) :
    0 ≤ c :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_spectrum_nonneg n hc

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    {c : ℝ}
    (hc : c ∈ spectrum ℝ
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n)) :
    c ≤ 1 :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_spectrum_le_one n hc

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    {c : ℝ}
    (hc : c ∈ spectrum ℝ
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n)) :
    c ∈ Set.Icc (0 : ℝ) 1 :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_spectrum_mem_Icc n hc

end

end MathlibAnalytic
end MGAP4D
