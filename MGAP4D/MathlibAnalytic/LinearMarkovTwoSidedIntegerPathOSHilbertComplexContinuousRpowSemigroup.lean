import MGAP4D.MathlibAnalytic.ComplexContinuousPositiveContractionRpow
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertComplexContinuousNNRpowSemigroup
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped ComplexOrder NNReal

namespace LinearMarkovTwoSidedIntegerPathOSPreHilbertData

variable {Ω : Type*} [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- The unital CFC real power of a natural-time complex temporal OS operator. -/
noncomputable def hilbertShiftSemigroupComplexContinuousRpow
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ)
    (x : ℝ) :
    D.HilbertAlgebraicComplexification →L[ℂ]
      D.HilbertAlgebraicComplexification :=
  ComplexContinuousPositiveContraction.rpow
    (D.hilbertShiftSemigroupComplexContinuousLinearMap n) x

/-- Every natural-time temporal OS unital real power is nonnegative. -/
theorem hilbertShiftSemigroupComplexContinuousRpow_nonneg
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ)
    (x : ℝ) :
    0 ≤ D.hilbertShiftSemigroupComplexContinuousRpow n x :=
  ComplexContinuousPositiveContraction.rpow_nonneg
    (D.hilbertShiftSemigroupComplexContinuousLinearMap n) x

/-- Every natural-time temporal OS unital real power is positive. -/
theorem hilbertShiftSemigroupComplexContinuousRpow_isPositive
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ)
    (x : ℝ) :
    (D.hilbertShiftSemigroupComplexContinuousRpow n x).IsPositive :=
  ComplexContinuousPositiveContraction.rpow_isPositive
    (D.hilbertShiftSemigroupComplexContinuousLinearMap n) x

/-- Every natural-time temporal OS unital real power is self-adjoint. -/
theorem hilbertShiftSemigroupComplexContinuousRpow_isSelfAdjoint
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ)
    (x : ℝ) :
    IsSelfAdjoint (D.hilbertShiftSemigroupComplexContinuousRpow n x) :=
  ComplexContinuousPositiveContraction.rpow_isSelfAdjoint
    (D.hilbertShiftSemigroupComplexContinuousLinearMap n) x

/-- Exponent zero gives the identity for every positive temporal OS operator. -/
@[simp]
theorem hilbertShiftSemigroupComplexContinuousRpow_zero
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (hquad : LinearMarkovTransitionQuadraticNonnegative D.initial D.transition)
    (n : ℕ) :
    D.hilbertShiftSemigroupComplexContinuousRpow n 0 = 1 :=
  ComplexContinuousPositiveContraction.rpow_zero
    (D.hilbertShiftSemigroupComplexContinuousLinearMap n)
    (D.hilbertShiftSemigroupComplexContinuousLinearMap_isPositive hquad n)

/-- Exponent one recovers the natural-time temporal OS operator. -/
theorem hilbertShiftSemigroupComplexContinuousRpow_one
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (hquad : LinearMarkovTransitionQuadraticNonnegative D.initial D.transition)
    (n : ℕ) :
    D.hilbertShiftSemigroupComplexContinuousRpow n 1 =
      D.hilbertShiftSemigroupComplexContinuousLinearMap n :=
  ComplexContinuousPositiveContraction.rpow_one
    (D.hilbertShiftSemigroupComplexContinuousLinearMap n)
    (D.hilbertShiftSemigroupComplexContinuousLinearMap_isPositive hquad n)

/-- Natural-number real exponents agree with ordinary operator powers. -/
theorem hilbertShiftSemigroupComplexContinuousRpow_natCast
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (hquad : LinearMarkovTransitionQuadraticNonnegative D.initial D.transition)
    (n m : ℕ) :
    D.hilbertShiftSemigroupComplexContinuousRpow n (m : ℝ) =
      (D.hilbertShiftSemigroupComplexContinuousLinearMap n) ^ m :=
  ComplexContinuousPositiveContraction.rpow_natCast
    (D.hilbertShiftSemigroupComplexContinuousLinearMap n) m
    (D.hilbertShiftSemigroupComplexContinuousLinearMap_isPositive hquad n)

/-- Positive real exponents agree with the preceding non-unital nonnegative
power construction. -/
theorem hilbertShiftSemigroupComplexContinuousRpow_coe_eq_NNRpow
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ)
    (p : ℝ≥0)
    (hp : 0 < p) :
    D.hilbertShiftSemigroupComplexContinuousRpow n (p : ℝ) =
      D.hilbertShiftSemigroupComplexContinuousNNRpow n p :=
  ComplexContinuousPositiveContraction.rpow_coe_eq_nnrpow
    (D.hilbertShiftSemigroupComplexContinuousLinearMap n) p hp

/-- Iterated temporal OS unital real powers multiply nonnegative exponents. -/
theorem hilbertShiftSemigroupComplexContinuousRpow_rpow_of_exponent_nonneg
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (hquad : LinearMarkovTransitionQuadraticNonnegative D.initial D.transition)
    (n : ℕ)
    (x y : ℝ)
    (hx : 0 ≤ x)
    (hy : 0 ≤ y) :
    ComplexContinuousPositiveContraction.rpow
        (D.hilbertShiftSemigroupComplexContinuousRpow n x) y =
      D.hilbertShiftSemigroupComplexContinuousRpow n (x * y) :=
  ComplexContinuousPositiveContraction.rpow_rpow_of_exponent_nonneg
    (D.hilbertShiftSemigroupComplexContinuousLinearMap n) x y hx hy
    (D.hilbertShiftSemigroupComplexContinuousLinearMap_isPositive hquad n)

/-- For exponents in `[0,1]`, every natural-time temporal OS unital real power
is at most the identity. -/
theorem hilbertShiftSemigroupComplexContinuousRpow_le_one
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ)
    (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    D.hilbertShiftSemigroupComplexContinuousRpow n x ≤ 1 :=
  ComplexContinuousPositiveContraction.rpow_le_one
    (D.hilbertShiftSemigroupComplexContinuousLinearMap n) x hx
    (D.hilbertShiftSemigroupComplexContinuousLinearMap_le_one n)

/-- For exponents in `[0,1]`, every natural-time temporal OS unital real power
belongs to `[0,I]`. -/
theorem hilbertShiftSemigroupComplexContinuousRpow_mem_Icc
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ)
    (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    D.hilbertShiftSemigroupComplexContinuousRpow n x ∈
      Set.Icc
        (0 : D.HilbertAlgebraicComplexification →L[ℂ]
          D.HilbertAlgebraicComplexification)
        1 :=
  ComplexContinuousPositiveContraction.rpow_mem_Icc
    (D.hilbertShiftSemigroupComplexContinuousLinearMap n) x hx
    (D.hilbertShiftSemigroupComplexContinuousLinearMap_le_one n)

/-- The real half-power is the canonical temporal OS square root. -/
theorem hilbertShiftSemigroupComplexContinuousRpow_one_div_two_eq_squareRoot
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ) :
    D.hilbertShiftSemigroupComplexContinuousRpow n (1 / 2 : ℝ) =
      D.hilbertShiftSemigroupComplexContinuousSquareRoot n :=
  ComplexContinuousPositiveContraction.rpow_one_div_two_eq_squareRoot
    (D.hilbertShiftSemigroupComplexContinuousLinearMap n)

/-- The unital real half-power of the time-`2n` operator is the time-`n`
operator. -/
theorem hilbertShiftSemigroupComplexContinuousRpow_one_div_two_two_mul_eq
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (hquad : LinearMarkovTransitionQuadraticNonnegative D.initial D.transition)
    (n : ℕ) :
    D.hilbertShiftSemigroupComplexContinuousRpow (2 * n) (1 / 2 : ℝ) =
      D.hilbertShiftSemigroupComplexContinuousLinearMap n := by
  calc
    D.hilbertShiftSemigroupComplexContinuousRpow (2 * n) (1 / 2 : ℝ) =
        D.hilbertShiftSemigroupComplexContinuousSquareRoot (2 * n) :=
      D.hilbertShiftSemigroupComplexContinuousRpow_one_div_two_eq_squareRoot
        (2 * n)
    _ = D.hilbertShiftSemigroupComplexContinuousLinearMap n :=
      D.hilbertShiftSemigroupComplexContinuousSquareRoot_two_mul_eq hquad n

/-- The unital real half-power of the two-step operator is the one-step shift. -/
theorem hilbertShiftSemigroupComplexContinuousRpow_one_div_two_two_eq_shift
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (hquad : LinearMarkovTransitionQuadraticNonnegative D.initial D.transition) :
    D.hilbertShiftSemigroupComplexContinuousRpow 2 (1 / 2 : ℝ) =
      D.hilbertShiftComplexContinuousLinearMap := by
  simpa using
    D.hilbertShiftSemigroupComplexContinuousRpow_one_div_two_two_mul_eq
      hquad 1

end LinearMarkovTwoSidedIntegerPathOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
