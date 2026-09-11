import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertLoewnerRayleighInterval
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertSpectrumInterval

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Every natural-time actual finite Wilson random-scan temporal OS operator has
operator norm at most one. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_opNorm_le_one
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    ‖L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n‖ ≤ 1 :=
  LinearMarkovTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroup_opNorm_le_one
    L.randomScanTwoSidedIntegerPathOSPreHilbertData n

/-- Every real spectral value of a natural-time actual finite Wilson random-scan
temporal OS operator is nonnegative. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_spectrum_nonneg
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    {c : ℝ}
    (hc : c ∈ spectrum ℝ
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n)) :
    0 ≤ c :=
  LinearMarkovTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroup_spectrum_nonneg
    L.randomScanTwoSidedIntegerPathOSPreHilbertData
    (finite_lattice_randomScanTransitionQuadraticNonnegative L) n hc

/-- Every real spectral value of a natural-time actual finite Wilson random-scan
temporal OS operator is at most one. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_spectrum_le_one
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    {c : ℝ}
    (hc : c ∈ spectrum ℝ
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n)) :
    c ≤ 1 :=
  LinearMarkovTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroup_spectrum_le_one
    L.randomScanTwoSidedIntegerPathOSPreHilbertData n hc

/-- The real spectrum of every natural-time actual finite Wilson random-scan
temporal OS operator is contained in `[0, 1]`. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_spectrum_subset_Icc
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    spectrum ℝ (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n) ⊆
      Set.Icc (0 : ℝ) 1 :=
  LinearMarkovTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroup_spectrum_subset_Icc
    L.randomScanTwoSidedIntegerPathOSPreHilbertData
    (finite_lattice_randomScanTransitionQuadraticNonnegative L) n

/-- Pointwise form of the actual finite Wilson temporal OS spectral interval
theorem. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_spectrum_mem_Icc
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    {c : ℝ}
    (hc : c ∈ spectrum ℝ
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n)) :
    c ∈ Set.Icc (0 : ℝ) 1 :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_spectrum_subset_Icc n hc

end

end MathlibAnalytic
end MGAP4D
