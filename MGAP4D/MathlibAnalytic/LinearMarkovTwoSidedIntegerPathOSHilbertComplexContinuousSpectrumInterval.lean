import MGAP4D.MathlibAnalytic.ComplexContinuousPositiveContractionSpectrumInterval
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertComplexContinuousLoewnerInterval

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped ComplexOrder

namespace LinearMarkovTwoSidedIntegerPathOSPreHilbertData

variable {Ω : Type*} [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- Every natural-time complex temporal OS operator has operator norm at most
one. -/
theorem hilbertShiftSemigroupComplexContinuousLinearMap_opNorm_le_one
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ) :
    ‖D.hilbertShiftSemigroupComplexContinuousLinearMap n‖ ≤ 1 :=
  ComplexContinuousPositiveContraction.opNorm_le_one
    (D.hilbertShiftSemigroupComplexContinuousLinearMap n)
    (fun x => D.norm_hilbertShiftSemigroupComplexContinuousLinearMap_le n x)

/-- Every real spectral value of a natural-time complex temporal OS operator is
nonnegative. -/
theorem hilbertShiftSemigroupComplexContinuousLinearMap_real_spectrum_nonneg
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (hquad : LinearMarkovTransitionQuadraticNonnegative D.initial D.transition)
    (n : ℕ)
    {r : ℝ}
    (hr : r ∈ spectrum ℝ
      (D.hilbertShiftSemigroupComplexContinuousLinearMap n)) :
    0 ≤ r :=
  ComplexContinuousPositiveContraction.real_spectrum_nonneg
    (D.hilbertShiftSemigroupComplexContinuousLinearMap n)
    (D.hilbertShiftSemigroupComplexContinuousLinearMap_isPositive hquad n)
    hr

/-- Every real spectral value of a natural-time complex temporal OS operator is
at most one. -/
theorem hilbertShiftSemigroupComplexContinuousLinearMap_real_spectrum_le_one
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ)
    {r : ℝ}
    (hr : r ∈ spectrum ℝ
      (D.hilbertShiftSemigroupComplexContinuousLinearMap n)) :
    r ≤ 1 :=
  ComplexContinuousPositiveContraction.real_spectrum_le_one
    (D.hilbertShiftSemigroupComplexContinuousLinearMap n)
    (fun x => D.norm_hilbertShiftSemigroupComplexContinuousLinearMap_le n x)
    hr

/-- The complex spectrum of every natural-time temporal OS operator is
contained in `[0, 1]`. -/
theorem hilbertShiftSemigroupComplexContinuousLinearMap_spectrum_subset_Icc
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (hquad : LinearMarkovTransitionQuadraticNonnegative D.initial D.transition)
    (n : ℕ) :
    spectrum ℂ (D.hilbertShiftSemigroupComplexContinuousLinearMap n) ⊆
      Set.Icc (0 : ℂ) 1 :=
  ComplexContinuousPositiveContraction.complex_spectrum_subset_Icc
    (D.hilbertShiftSemigroupComplexContinuousLinearMap n)
    (D.hilbertShiftSemigroupComplexContinuousLinearMap_isPositive hquad n)
    (fun x => D.norm_hilbertShiftSemigroupComplexContinuousLinearMap_le n x)

/-- Pointwise complex spectral interval theorem for every natural-time temporal
OS operator. -/
theorem hilbertShiftSemigroupComplexContinuousLinearMap_spectrum_mem_Icc
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (hquad : LinearMarkovTransitionQuadraticNonnegative D.initial D.transition)
    (n : ℕ)
    {c : ℂ}
    (hc : c ∈ spectrum ℂ
      (D.hilbertShiftSemigroupComplexContinuousLinearMap n)) :
    c ∈ Set.Icc (0 : ℂ) 1 :=
  D.hilbertShiftSemigroupComplexContinuousLinearMap_spectrum_subset_Icc hquad n hc

/-- The one-step complex temporal OS operator has operator norm at most one. -/
theorem hilbertShiftComplexContinuousLinearMap_opNorm_le_one
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω) :
    ‖D.hilbertShiftComplexContinuousLinearMap‖ ≤ 1 :=
  ComplexContinuousPositiveContraction.opNorm_le_one
    D.hilbertShiftComplexContinuousLinearMap
    (fun x => D.norm_hilbertShiftComplexContinuousLinearMap_le x)

/-- The complex spectrum of the one-step temporal OS shift is contained in
`[0, 1]`. -/
theorem hilbertShiftComplexContinuousLinearMap_spectrum_subset_Icc
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (hquad : LinearMarkovTransitionQuadraticNonnegative D.initial D.transition) :
    spectrum ℂ D.hilbertShiftComplexContinuousLinearMap ⊆
      Set.Icc (0 : ℂ) 1 :=
  ComplexContinuousPositiveContraction.complex_spectrum_subset_Icc
    D.hilbertShiftComplexContinuousLinearMap
    (D.hilbertShiftComplexContinuousLinearMap_isPositive hquad)
    (fun x => D.norm_hilbertShiftComplexContinuousLinearMap_le x)

/-- Pointwise complex spectral interval theorem for the one-step temporal OS
shift. -/
theorem hilbertShiftComplexContinuousLinearMap_spectrum_mem_Icc
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (hquad : LinearMarkovTransitionQuadraticNonnegative D.initial D.transition)
    {c : ℂ}
    (hc : c ∈ spectrum ℂ D.hilbertShiftComplexContinuousLinearMap) :
    c ∈ Set.Icc (0 : ℂ) 1 :=
  D.hilbertShiftComplexContinuousLinearMap_spectrum_subset_Icc hquad hc

end LinearMarkovTwoSidedIntegerPathOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
