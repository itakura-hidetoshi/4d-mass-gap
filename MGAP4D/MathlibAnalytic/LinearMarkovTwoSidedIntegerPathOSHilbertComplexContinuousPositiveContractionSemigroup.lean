import MGAP4D.MathlibAnalytic.RealTensorComplexificationContinuousPositiveContraction
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertPositiveSelfAdjoint
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertComplexContinuousSelfAdjointContractionSemigroup

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace LinearMarkovTwoSidedIntegerPathOSPreHilbertData

variable {Ω : Type*} [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- Every natural-time continuous complex temporal OS operator has nonnegative
real quadratic form once the real transition quadratic form is nonnegative. -/
theorem re_inner_hilbertShiftSemigroupComplexContinuousLinearMap_self_nonneg
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (hquad : LinearMarkovTransitionQuadraticNonnegative D.initial D.transition)
    (n : ℕ)
    (x : D.HilbertAlgebraicComplexification) :
    0 ≤ (inner ℂ
      (D.hilbertShiftSemigroupComplexContinuousLinearMap n x) x).re :=
  RealTensorComplexification.re_inner_ofContinuousLinearMapContraction_self_nonneg
    (D.hilbertShiftSemigroup n)
    (fun u => D.norm_hilbertShiftSemigroup_le n u)
    (fun u => D.inner_hilbertShiftSemigroup_self_nonneg hquad n u)
    x

/-- Every natural-time continuous complex temporal OS operator is positive in
Mathlib's bundled sense. -/
theorem hilbertShiftSemigroupComplexContinuousLinearMap_isPositive
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (hquad : LinearMarkovTransitionQuadraticNonnegative D.initial D.transition)
    (n : ℕ) :
    (D.hilbertShiftSemigroupComplexContinuousLinearMap n).IsPositive :=
  RealTensorComplexification.isPositive_ofContinuousLinearMapContraction
    (D.hilbertShiftSemigroup n)
    (fun u => D.norm_hilbertShiftSemigroup_le n u)
    (fun u v => D.inner_hilbertShiftSemigroup_left_eq_right n u v)
    (fun u => D.inner_hilbertShiftSemigroup_self_nonneg hquad n u)

/-- Every natural-time continuous complex temporal OS operator is nonnegative in
the Loewner order. -/
theorem hilbertShiftSemigroupComplexContinuousLinearMap_nonneg
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (hquad : LinearMarkovTransitionQuadraticNonnegative D.initial D.transition)
    (n : ℕ) :
    0 ≤ D.hilbertShiftSemigroupComplexContinuousLinearMap n :=
  RealTensorComplexification.nonneg_ofContinuousLinearMapContraction
    (D.hilbertShiftSemigroup n)
    (fun u => D.norm_hilbertShiftSemigroup_le n u)
    (fun u v => D.inner_hilbertShiftSemigroup_left_eq_right n u v)
    (fun u => D.inner_hilbertShiftSemigroup_self_nonneg hquad n u)

/-- The one-step continuous complex temporal OS shift has nonnegative real
quadratic form. -/
theorem re_inner_hilbertShiftComplexContinuousLinearMap_self_nonneg
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (hquad : LinearMarkovTransitionQuadraticNonnegative D.initial D.transition)
    (x : D.HilbertAlgebraicComplexification) :
    0 ≤ (inner ℂ (D.hilbertShiftComplexContinuousLinearMap x) x).re := by
  simpa only [D.hilbertShiftSemigroupComplexContinuousLinearMap_one] using
    D.re_inner_hilbertShiftSemigroupComplexContinuousLinearMap_self_nonneg
      hquad 1 x

/-- The one-step continuous complex temporal OS shift is positive. -/
theorem hilbertShiftComplexContinuousLinearMap_isPositive
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (hquad : LinearMarkovTransitionQuadraticNonnegative D.initial D.transition) :
    D.hilbertShiftComplexContinuousLinearMap.IsPositive := by
  rw [← D.hilbertShiftSemigroupComplexContinuousLinearMap_one]
  exact D.hilbertShiftSemigroupComplexContinuousLinearMap_isPositive hquad 1

/-- The one-step continuous complex temporal OS shift is nonnegative in the
Loewner order. -/
theorem hilbertShiftComplexContinuousLinearMap_nonneg
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (hquad : LinearMarkovTransitionQuadraticNonnegative D.initial D.transition) :
    0 ≤ D.hilbertShiftComplexContinuousLinearMap := by
  rw [← D.hilbertShiftSemigroupComplexContinuousLinearMap_one]
  exact D.hilbertShiftSemigroupComplexContinuousLinearMap_nonneg hquad 1

end LinearMarkovTwoSidedIntegerPathOSPreHilbertData

end
end MathlibAnalytic
end MGAP4D
