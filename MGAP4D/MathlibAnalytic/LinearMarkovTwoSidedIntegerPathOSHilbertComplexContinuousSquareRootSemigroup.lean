import MGAP4D.MathlibAnalytic.ComplexContinuousPositiveContractionSquareRoot
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertComplexContinuousLoewnerInterval
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped ComplexOrder

namespace LinearMarkovTwoSidedIntegerPathOSPreHilbertData

variable {Ω : Type*} [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- Canonical CFC square root of the natural-time complex temporal OS
operator. -/
noncomputable def hilbertShiftSemigroupComplexContinuousSquareRoot
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ) :
    D.HilbertAlgebraicComplexification →L[ℂ]
      D.HilbertAlgebraicComplexification :=
  ComplexContinuousPositiveContraction.squareRoot
    (D.hilbertShiftSemigroupComplexContinuousLinearMap n)

/-- Every natural-time temporal OS CFC square root is nonnegative. -/
theorem hilbertShiftSemigroupComplexContinuousSquareRoot_nonneg
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ) :
    0 ≤ D.hilbertShiftSemigroupComplexContinuousSquareRoot n :=
  ComplexContinuousPositiveContraction.squareRoot_nonneg
    (D.hilbertShiftSemigroupComplexContinuousLinearMap n)

/-- Every natural-time temporal OS CFC square root is positive in the bundled
sense. -/
theorem hilbertShiftSemigroupComplexContinuousSquareRoot_isPositive
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ) :
    (D.hilbertShiftSemigroupComplexContinuousSquareRoot n).IsPositive :=
  ComplexContinuousPositiveContraction.squareRoot_isPositive
    (D.hilbertShiftSemigroupComplexContinuousLinearMap n)

/-- Every natural-time temporal OS CFC square root is self-adjoint. -/
theorem hilbertShiftSemigroupComplexContinuousSquareRoot_isSelfAdjoint
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ) :
    IsSelfAdjoint (D.hilbertShiftSemigroupComplexContinuousSquareRoot n) :=
  ComplexContinuousPositiveContraction.squareRoot_isSelfAdjoint
    (D.hilbertShiftSemigroupComplexContinuousLinearMap n)

/-- The CFC square root squares to the natural-time temporal OS operator. -/
theorem hilbertShiftSemigroupComplexContinuousSquareRoot_mul_self_eq
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (hquad : LinearMarkovTransitionQuadraticNonnegative D.initial D.transition)
    (n : ℕ) :
    D.hilbertShiftSemigroupComplexContinuousSquareRoot n *
        D.hilbertShiftSemigroupComplexContinuousSquareRoot n =
      D.hilbertShiftSemigroupComplexContinuousLinearMap n :=
  ComplexContinuousPositiveContraction.squareRoot_mul_self_eq
    (D.hilbertShiftSemigroupComplexContinuousLinearMap n)
    (D.hilbertShiftSemigroupComplexContinuousLinearMap_isPositive hquad n)

/-- Every natural-time temporal OS square root is at most the identity. -/
theorem hilbertShiftSemigroupComplexContinuousSquareRoot_le_one
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ) :
    D.hilbertShiftSemigroupComplexContinuousSquareRoot n ≤ 1 :=
  ComplexContinuousPositiveContraction.squareRoot_le_one
    (D.hilbertShiftSemigroupComplexContinuousLinearMap n)
    (D.hilbertShiftSemigroupComplexContinuousLinearMap_le_one n)

/-- Every natural-time temporal OS square root belongs to `[0, I]`. -/
theorem hilbertShiftSemigroupComplexContinuousSquareRoot_mem_Icc
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ) :
    D.hilbertShiftSemigroupComplexContinuousSquareRoot n ∈
      Set.Icc
        (0 : D.HilbertAlgebraicComplexification →L[ℂ]
          D.HilbertAlgebraicComplexification)
        1 :=
  ⟨D.hilbertShiftSemigroupComplexContinuousSquareRoot_nonneg n,
    D.hilbertShiftSemigroupComplexContinuousSquareRoot_le_one n⟩

/-- The natural-time temporal OS operator is the canonical nonnegative square
root of its even-time member. -/
theorem hilbertShiftSemigroupComplexContinuousSquareRoot_two_mul_eq
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (hquad : LinearMarkovTransitionQuadraticNonnegative D.initial D.transition)
    (n : ℕ) :
    D.hilbertShiftSemigroupComplexContinuousSquareRoot (2 * n) =
      D.hilbertShiftSemigroupComplexContinuousLinearMap n := by
  unfold hilbertShiftSemigroupComplexContinuousSquareRoot
  apply
    ComplexContinuousPositiveContraction.squareRoot_eq_of_nonneg_mul_self_eq
  · exact D.hilbertShiftSemigroupComplexContinuousLinearMap_nonneg hquad n
  · rw [show 2 * n = n + n by omega,
      D.hilbertShiftSemigroupComplexContinuousLinearMap_add]
    rfl

/-- The one-step temporal OS operator is the canonical square root of the
two-step operator. -/
theorem hilbertShiftSemigroupComplexContinuousSquareRoot_two_eq_shift
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (hquad : LinearMarkovTransitionQuadraticNonnegative D.initial D.transition) :
    D.hilbertShiftSemigroupComplexContinuousSquareRoot 2 =
      D.hilbertShiftComplexContinuousLinearMap := by
  simpa using
    D.hilbertShiftSemigroupComplexContinuousSquareRoot_two_mul_eq hquad 1

end LinearMarkovTwoSidedIntegerPathOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
