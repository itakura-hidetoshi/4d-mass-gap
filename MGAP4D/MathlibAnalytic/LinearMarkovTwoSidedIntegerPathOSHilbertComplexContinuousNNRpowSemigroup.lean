import MGAP4D.MathlibAnalytic.ComplexContinuousPositiveContractionNNRpow
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertComplexContinuousSquareRootSemigroup
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped ComplexOrder NNReal

namespace LinearMarkovTwoSidedIntegerPathOSPreHilbertData

variable {Ω : Type*} [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- The CFC nonnegative power of a natural-time complex temporal OS operator. -/
noncomputable def hilbertShiftSemigroupComplexContinuousNNRpow
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ)
    (p : ℝ≥0) :
    D.HilbertAlgebraicComplexification →L[ℂ]
      D.HilbertAlgebraicComplexification :=
  ComplexContinuousPositiveContraction.nnrpow
    (D.hilbertShiftSemigroupComplexContinuousLinearMap n) p

/-- Every natural-time temporal OS CFC nonnegative power is nonnegative. -/
theorem hilbertShiftSemigroupComplexContinuousNNRpow_nonneg
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ)
    (p : ℝ≥0) :
    0 ≤ D.hilbertShiftSemigroupComplexContinuousNNRpow n p :=
  ComplexContinuousPositiveContraction.nnrpow_nonneg
    (D.hilbertShiftSemigroupComplexContinuousLinearMap n) p

/-- Every natural-time temporal OS CFC nonnegative power is positive in the
bundled sense. -/
theorem hilbertShiftSemigroupComplexContinuousNNRpow_isPositive
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ)
    (p : ℝ≥0) :
    (D.hilbertShiftSemigroupComplexContinuousNNRpow n p).IsPositive :=
  ComplexContinuousPositiveContraction.nnrpow_isPositive
    (D.hilbertShiftSemigroupComplexContinuousLinearMap n) p

/-- Every natural-time temporal OS CFC nonnegative power is self-adjoint. -/
theorem hilbertShiftSemigroupComplexContinuousNNRpow_isSelfAdjoint
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ)
    (p : ℝ≥0) :
    IsSelfAdjoint (D.hilbertShiftSemigroupComplexContinuousNNRpow n p) :=
  ComplexContinuousPositiveContraction.nnrpow_isSelfAdjoint
    (D.hilbertShiftSemigroupComplexContinuousLinearMap n) p

/-- Exponent zero follows the non-unital CFC convention and gives zero. -/
@[simp]
theorem hilbertShiftSemigroupComplexContinuousNNRpow_zero
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ) :
    D.hilbertShiftSemigroupComplexContinuousNNRpow n 0 = 0 :=
  ComplexContinuousPositiveContraction.nnrpow_zero
    (D.hilbertShiftSemigroupComplexContinuousLinearMap n)

/-- Exponent one recovers the natural-time temporal OS operator. -/
theorem hilbertShiftSemigroupComplexContinuousNNRpow_one
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (hquad : LinearMarkovTransitionQuadraticNonnegative D.initial D.transition)
    (n : ℕ) :
    D.hilbertShiftSemigroupComplexContinuousNNRpow n 1 =
      D.hilbertShiftSemigroupComplexContinuousLinearMap n :=
  ComplexContinuousPositiveContraction.nnrpow_one
    (D.hilbertShiftSemigroupComplexContinuousLinearMap n)
    (D.hilbertShiftSemigroupComplexContinuousLinearMap_isPositive hquad n)

/-- Positive exponents add under multiplication for each natural-time temporal
OS operator. -/
theorem hilbertShiftSemigroupComplexContinuousNNRpow_add
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ)
    {p q : ℝ≥0}
    (hp : 0 < p)
    (hq : 0 < q) :
    D.hilbertShiftSemigroupComplexContinuousNNRpow n (p + q) =
      D.hilbertShiftSemigroupComplexContinuousNNRpow n p *
        D.hilbertShiftSemigroupComplexContinuousNNRpow n q :=
  ComplexContinuousPositiveContraction.nnrpow_add
    (D.hilbertShiftSemigroupComplexContinuousLinearMap n) hp hq

/-- Iterated CFC nonnegative powers multiply their exponents. -/
theorem hilbertShiftSemigroupComplexContinuousNNRpow_nnrpow
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ)
    (p q : ℝ≥0) :
    ComplexContinuousPositiveContraction.nnrpow
        (D.hilbertShiftSemigroupComplexContinuousNNRpow n p) q =
      D.hilbertShiftSemigroupComplexContinuousNNRpow n (p * q) :=
  ComplexContinuousPositiveContraction.nnrpow_nnrpow
    (D.hilbertShiftSemigroupComplexContinuousLinearMap n) p q

/-- For exponents in `[0,1]`, every natural-time temporal OS nonnegative power
is at most the identity. -/
theorem hilbertShiftSemigroupComplexContinuousNNRpow_le_one
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ)
    (p : ℝ≥0)
    (hp : p ∈ Set.Icc (0 : ℝ≥0) 1) :
    D.hilbertShiftSemigroupComplexContinuousNNRpow n p ≤ 1 :=
  ComplexContinuousPositiveContraction.nnrpow_le_one
    (D.hilbertShiftSemigroupComplexContinuousLinearMap n) p hp
    (D.hilbertShiftSemigroupComplexContinuousLinearMap_le_one n)

/-- For exponents in `[0,1]`, every natural-time temporal OS nonnegative power
belongs to `[0,I]`. -/
theorem hilbertShiftSemigroupComplexContinuousNNRpow_mem_Icc
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ)
    (p : ℝ≥0)
    (hp : p ∈ Set.Icc (0 : ℝ≥0) 1) :
    D.hilbertShiftSemigroupComplexContinuousNNRpow n p ∈
      Set.Icc
        (0 : D.HilbertAlgebraicComplexification →L[ℂ]
          D.HilbertAlgebraicComplexification)
        1 :=
  ComplexContinuousPositiveContraction.nnrpow_mem_Icc
    (D.hilbertShiftSemigroupComplexContinuousLinearMap n) p hp
    (D.hilbertShiftSemigroupComplexContinuousLinearMap_le_one n)

/-- The exponent `1 / 2` temporal OS nonnegative power is the canonical square
root constructed in the preceding layer. -/
theorem hilbertShiftSemigroupComplexContinuousNNRpow_one_div_two_eq_squareRoot
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ) :
    D.hilbertShiftSemigroupComplexContinuousNNRpow n (1 / 2 : ℝ≥0) =
      D.hilbertShiftSemigroupComplexContinuousSquareRoot n :=
  ComplexContinuousPositiveContraction.nnrpow_one_div_two_eq_squareRoot
    (D.hilbertShiftSemigroupComplexContinuousLinearMap n)

/-- The half-power of the time-`2n` temporal OS operator is the time-`n`
operator. -/
theorem hilbertShiftSemigroupComplexContinuousNNRpow_one_div_two_two_mul_eq
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (hquad : LinearMarkovTransitionQuadraticNonnegative D.initial D.transition)
    (n : ℕ) :
    D.hilbertShiftSemigroupComplexContinuousNNRpow (2 * n) (1 / 2 : ℝ≥0) =
      D.hilbertShiftSemigroupComplexContinuousLinearMap n := by
  calc
    D.hilbertShiftSemigroupComplexContinuousNNRpow (2 * n) (1 / 2 : ℝ≥0) =
        D.hilbertShiftSemigroupComplexContinuousSquareRoot (2 * n) :=
      D.hilbertShiftSemigroupComplexContinuousNNRpow_one_div_two_eq_squareRoot
        (2 * n)
    _ = D.hilbertShiftSemigroupComplexContinuousLinearMap n :=
      D.hilbertShiftSemigroupComplexContinuousSquareRoot_two_mul_eq hquad n

/-- The half-power of the two-step temporal OS operator is the one-step shift. -/
theorem hilbertShiftSemigroupComplexContinuousNNRpow_one_div_two_two_eq_shift
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (hquad : LinearMarkovTransitionQuadraticNonnegative D.initial D.transition) :
    D.hilbertShiftSemigroupComplexContinuousNNRpow 2 (1 / 2 : ℝ≥0) =
      D.hilbertShiftComplexContinuousLinearMap := by
  simpa using
    D.hilbertShiftSemigroupComplexContinuousNNRpow_one_div_two_two_mul_eq
      hquad 1

end LinearMarkovTwoSidedIntegerPathOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
