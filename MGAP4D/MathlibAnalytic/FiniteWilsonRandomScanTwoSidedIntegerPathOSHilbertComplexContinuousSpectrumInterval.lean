import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertComplexContinuousLoewnerInterval
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertComplexContinuousSpectrumInterval

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped ComplexOrder

/-- Every actual finite Wilson natural-time complex temporal OS operator has
operator norm at most one. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap_opNorm_le_one
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    ‖L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n‖ ≤ 1 :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupComplexContinuousLinearMap_opNorm_le_one n

/-- Every real spectral value of an actual finite Wilson natural-time complex
temporal OS operator is nonnegative. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap_real_spectrum_nonneg
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    {r : ℝ}
    (hr : r ∈ spectrum ℝ
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n)) :
    0 ≤ r :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupComplexContinuousLinearMap_real_spectrum_nonneg
    (finite_lattice_randomScanTransitionQuadraticNonnegative L) n hr

/-- Every real spectral value of an actual finite Wilson natural-time complex
temporal OS operator is at most one. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap_real_spectrum_le_one
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    {r : ℝ}
    (hr : r ∈ spectrum ℝ
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n)) :
    r ≤ 1 :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupComplexContinuousLinearMap_real_spectrum_le_one
    n hr

/-- The complex spectrum of every actual finite Wilson natural-time temporal OS
operator is contained in `[0, 1]`. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap_spectrum_subset_Icc
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    spectrum ℂ
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n) ⊆
      Set.Icc (0 : ℂ) 1 :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupComplexContinuousLinearMap_spectrum_subset_Icc
    (finite_lattice_randomScanTransitionQuadraticNonnegative L) n

/-- Pointwise complex spectral interval theorem for every actual finite Wilson
natural-time temporal OS operator. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap_spectrum_mem_Icc
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    {c : ℂ}
    (hc : c ∈ spectrum ℂ
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n)) :
    c ∈ Set.Icc (0 : ℂ) 1 :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap_spectrum_subset_Icc n hc

/-- The actual finite Wilson one-step complex temporal OS operator has operator
norm at most one. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap_opNorm_le_one
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    ‖L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap‖ ≤ 1 :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftComplexContinuousLinearMap_opNorm_le_one

/-- The complex spectrum of the actual finite Wilson one-step temporal OS shift
is contained in `[0, 1]`. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap_spectrum_subset_Icc
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    spectrum ℂ
        L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap ⊆
      Set.Icc (0 : ℂ) 1 :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftComplexContinuousLinearMap_spectrum_subset_Icc
    (finite_lattice_randomScanTransitionQuadraticNonnegative L)

/-- Pointwise complex spectral interval theorem for the actual finite Wilson
one-step temporal OS shift. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap_spectrum_mem_Icc
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    {c : ℂ}
    (hc : c ∈ spectrum ℂ
      L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap) :
    c ∈ Set.Icc (0 : ℂ) 1 :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap_spectrum_subset_Icc hc

end

end MathlibAnalytic
end MGAP4D
