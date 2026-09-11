import MGAP4D.MathlibAnalytic.ComplexContinuousPositiveContractionSpectrumInterval
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped ComplexOrder

namespace ComplexContinuousPositiveContraction

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The canonical continuous-functional-calculus square root of a complex
continuous linear operator. -/
noncomputable def squareRoot (T : H →L[ℂ] H) : H →L[ℂ] H :=
  CFC.sqrt T

@[simp]
theorem squareRoot_eq_cfc_sqrt (T : H →L[ℂ] H) :
    squareRoot T = CFC.sqrt T :=
  rfl

/-- The canonical CFC square root is nonnegative. -/
theorem squareRoot_nonneg (T : H →L[ℂ] H) :
    0 ≤ squareRoot T := by
  exact CFC.sqrt_nonneg T

/-- The canonical CFC square root is positive in the bundled
`ContinuousLinearMap.IsPositive` sense. -/
theorem squareRoot_isPositive (T : H →L[ℂ] H) :
    (squareRoot T).IsPositive :=
  (ContinuousLinearMap.nonneg_iff_isPositive (squareRoot T)).1
    (squareRoot_nonneg T)

/-- The canonical CFC square root is self-adjoint. -/
theorem squareRoot_isSelfAdjoint (T : H →L[ℂ] H) :
    IsSelfAdjoint (squareRoot T) :=
  (squareRoot_isPositive T).isSelfAdjoint

/-- The canonical square root squares to the original positive operator. -/
theorem squareRoot_mul_self_eq
    (T : H →L[ℂ] H)
    (hpositive : T.IsPositive) :
    squareRoot T * squareRoot T = T := by
  exact CFC.sqrt_mul_sqrt_self T
    ((ContinuousLinearMap.nonneg_iff_isPositive T).2 hpositive)

/-- Power-notation form of the square-root identity. -/
theorem squareRoot_sq_eq
    (T : H →L[ℂ] H)
    (hpositive : T.IsPositive) :
    (squareRoot T) ^ 2 = T := by
  simpa [pow_two] using squareRoot_mul_self_eq T hpositive

/-- The CFC square root is operator monotone, hence preserves the upper bound
by the identity. -/
theorem squareRoot_le_one
    (T : H →L[ℂ] H)
    (hle : T ≤ 1) :
    squareRoot T ≤ 1 := by
  simpa using CFC.sqrt_le_sqrt T (1 : H →L[ℂ] H) hle

/-- The square root of an operator in `[0, I]` again belongs to `[0, I]`. -/
theorem squareRoot_mem_Icc
    (T : H →L[ℂ] H)
    (hle : T ≤ 1) :
    squareRoot T ∈ Set.Icc (0 : H →L[ℂ] H) 1 :=
  ⟨squareRoot_nonneg T, squareRoot_le_one T hle⟩

/-- Uniqueness of the nonnegative square root. -/
theorem squareRoot_eq_of_nonneg_mul_self_eq
    (T S : H →L[ℂ] H)
    (hS : 0 ≤ S)
    (hSq : S * S = T) :
    squareRoot T = S := by
  exact CFC.sqrt_unique hSq hS

end ComplexContinuousPositiveContraction

end

end MathlibAnalytic
end MGAP4D
