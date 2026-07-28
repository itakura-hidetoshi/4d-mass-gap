import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertSpectrumInterval
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertSpectralRadius

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped ENNReal NNReal

/-- The real spectral radius of every natural-time actual finite Wilson
random-scan temporal OS operator equals its operator `nnnorm`. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_spectralRadius_eq_nnnorm
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    spectralRadius ℝ
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n) =
      (‖L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n‖₊ : ℝ≥0∞) :=
  LinearMarkovTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroup_spectralRadius_eq_nnnorm
    L.randomScanTwoSidedIntegerPathOSPreHilbertData
    (finite_lattice_randomScanTransitionQuadraticNonnegative L) n

/-- Every natural-time actual finite Wilson random-scan temporal OS operator has
`nnnorm` at most one. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_nnnorm_le_one
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    ‖L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n‖₊ ≤ 1 :=
  LinearMarkovTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroup_nnnorm_le_one
    L.randomScanTwoSidedIntegerPathOSPreHilbertData n

/-- Every natural-time actual finite Wilson random-scan temporal OS spectral
radius is at most one. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_spectralRadius_le_one
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    spectralRadius ℝ
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n) ≤ 1 :=
  LinearMarkovTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroup_spectralRadius_le_one
    L.randomScanTwoSidedIntegerPathOSPreHilbertData
    (finite_lattice_randomScanTransitionQuadraticNonnegative L) n

/-- The finite real value of every natural-time actual finite Wilson random-scan
temporal OS spectral radius is exactly the operator norm. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_spectralRadius_toReal_eq_norm
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    (spectralRadius ℝ
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n)).toReal =
      ‖L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n‖ :=
  LinearMarkovTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroup_spectralRadius_toReal_eq_norm
    L.randomScanTwoSidedIntegerPathOSPreHilbertData
    (finite_lattice_randomScanTransitionQuadraticNonnegative L) n

/-- Every natural-time actual finite Wilson random-scan temporal OS spectral
radius belongs to `[0, 1]`. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_spectralRadius_mem_Icc
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    spectralRadius ℝ
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n) ∈
        Set.Icc (0 : ℝ≥0∞) 1 :=
  LinearMarkovTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroup_spectralRadius_mem_Icc
    L.randomScanTwoSidedIntegerPathOSPreHilbertData
    (finite_lattice_randomScanTransitionQuadraticNonnegative L) n

end

end MathlibAnalytic
end MGAP4D
