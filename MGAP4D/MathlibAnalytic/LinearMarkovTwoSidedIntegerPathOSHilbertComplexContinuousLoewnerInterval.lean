import MGAP4D.MathlibAnalytic.ComplexContinuousSymmetricContractionLoewnerInterval
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertComplexContinuousPositiveContractionSemigroup

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped ComplexOrder

namespace LinearMarkovTwoSidedIntegerPathOSPreHilbertData

variable {Ω : Type*} [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- Every natural-time complex temporal OS quadratic form is bounded above by
that of the identity. -/
theorem re_inner_hilbertShiftSemigroupComplexContinuousLinearMap_self_le
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ)
    (x : D.HilbertAlgebraicComplexification) :
    (inner ℂ
      (D.hilbertShiftSemigroupComplexContinuousLinearMap n x) x).re ≤
      (inner ℂ x x).re :=
  ComplexContinuousSymmetricContraction.re_inner_apply_self_le
    (D.hilbertShiftSemigroupComplexContinuousLinearMap n)
    (fun y => D.norm_hilbertShiftSemigroupComplexContinuousLinearMap_le n y)
    x

/-- The complement of every natural-time complex temporal OS operator is
positive. -/
theorem one_sub_hilbertShiftSemigroupComplexContinuousLinearMap_isPositive
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ) :
    ((1 : D.HilbertAlgebraicComplexification →L[ℂ]
        D.HilbertAlgebraicComplexification) -
      D.hilbertShiftSemigroupComplexContinuousLinearMap n).IsPositive :=
  ComplexContinuousSymmetricContraction.one_sub_isPositive
    (D.hilbertShiftSemigroupComplexContinuousLinearMap n)
    (D.isSymmetric_hilbertShiftSemigroupComplexContinuousLinearMap n)
    (fun y => D.norm_hilbertShiftSemigroupComplexContinuousLinearMap_le n y)

/-- Every natural-time complex temporal OS operator is at most the identity in
Mathlib's Loewner order. -/
theorem hilbertShiftSemigroupComplexContinuousLinearMap_le_one
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ) :
    D.hilbertShiftSemigroupComplexContinuousLinearMap n ≤ 1 :=
  ComplexContinuousSymmetricContraction.le_one
    (D.hilbertShiftSemigroupComplexContinuousLinearMap n)
    (D.isSymmetric_hilbertShiftSemigroupComplexContinuousLinearMap n)
    (fun y => D.norm_hilbertShiftSemigroupComplexContinuousLinearMap_le n y)

/-- Every positive natural-time complex temporal OS operator belongs to the
Loewner interval `[0, I]`. -/
theorem hilbertShiftSemigroupComplexContinuousLinearMap_mem_Icc
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (hquad : LinearMarkovTransitionQuadraticNonnegative D.initial D.transition)
    (n : ℕ) :
    D.hilbertShiftSemigroupComplexContinuousLinearMap n ∈
      Set.Icc
        (0 : D.HilbertAlgebraicComplexification →L[ℂ]
          D.HilbertAlgebraicComplexification)
        1 :=
  ⟨D.hilbertShiftSemigroupComplexContinuousLinearMap_nonneg hquad n,
    D.hilbertShiftSemigroupComplexContinuousLinearMap_le_one n⟩

/-- The one-step complex temporal OS quadratic form is bounded above by that of
the identity. -/
theorem re_inner_hilbertShiftComplexContinuousLinearMap_self_le
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (x : D.HilbertAlgebraicComplexification) :
    (inner ℂ (D.hilbertShiftComplexContinuousLinearMap x) x).re ≤
      (inner ℂ x x).re := by
  simpa only [D.hilbertShiftSemigroupComplexContinuousLinearMap_one] using
    D.re_inner_hilbertShiftSemigroupComplexContinuousLinearMap_self_le 1 x

/-- The complement of the one-step complex temporal OS shift is positive. -/
theorem one_sub_hilbertShiftComplexContinuousLinearMap_isPositive
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω) :
    ((1 : D.HilbertAlgebraicComplexification →L[ℂ]
        D.HilbertAlgebraicComplexification) -
      D.hilbertShiftComplexContinuousLinearMap).IsPositive := by
  rw [← D.hilbertShiftSemigroupComplexContinuousLinearMap_one]
  exact D.one_sub_hilbertShiftSemigroupComplexContinuousLinearMap_isPositive 1

/-- The one-step complex temporal OS shift is at most the identity. -/
theorem hilbertShiftComplexContinuousLinearMap_le_one
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω) :
    D.hilbertShiftComplexContinuousLinearMap ≤ 1 := by
  rw [← D.hilbertShiftSemigroupComplexContinuousLinearMap_one]
  exact D.hilbertShiftSemigroupComplexContinuousLinearMap_le_one 1

/-- The positive one-step complex temporal OS shift belongs to `[0, I]`. -/
theorem hilbertShiftComplexContinuousLinearMap_mem_Icc
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (hquad : LinearMarkovTransitionQuadraticNonnegative D.initial D.transition) :
    D.hilbertShiftComplexContinuousLinearMap ∈
      Set.Icc
        (0 : D.HilbertAlgebraicComplexification →L[ℂ]
          D.HilbertAlgebraicComplexification)
        1 :=
  ⟨D.hilbertShiftComplexContinuousLinearMap_nonneg hquad,
    D.hilbertShiftComplexContinuousLinearMap_le_one⟩

end LinearMarkovTwoSidedIntegerPathOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
