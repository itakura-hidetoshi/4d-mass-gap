import MGAP4D.MathlibAnalytic.RealTensorComplexificationContinuousSymmetricContraction
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertComplexContinuousContractionSemigroup
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace LinearMarkovTwoSidedIntegerPathOSPreHilbertData

variable {Ω : Type*} [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- The continuous complexified one-step temporal OS shift is symmetric for the
canonical complex inner product. -/
theorem inner_hilbertShiftComplexContinuousLinearMap_left_eq_right
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (x y : D.HilbertAlgebraicComplexification) :
    inner ℂ (D.hilbertShiftComplexContinuousLinearMap x) y =
      inner ℂ x (D.hilbertShiftComplexContinuousLinearMap y) := by
  exact
    RealTensorComplexification.inner_ofContinuousLinearMapContraction_left_eq_right
      D.hilbertShiftContinuousLinearMap
      (fun u => D.norm_hilbertShiftContinuousLinearMap_le u)
      (fun u v => D.inner_hilbertShiftContinuousLinearMap_left_eq_right u v)
      x y

/-- Every natural-time member of the continuous complex temporal OS semigroup
is symmetric for the canonical complex inner product. -/
theorem inner_hilbertShiftSemigroupComplexContinuousLinearMap_left_eq_right
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ)
    (x y : D.HilbertAlgebraicComplexification) :
    inner ℂ (D.hilbertShiftSemigroupComplexContinuousLinearMap n x) y =
      inner ℂ x (D.hilbertShiftSemigroupComplexContinuousLinearMap n y) := by
  exact
    RealTensorComplexification.inner_ofContinuousLinearMapContraction_left_eq_right
      (D.hilbertShiftSemigroup n)
      (fun u => D.norm_hilbertShiftSemigroup_le n u)
      (fun u v => D.inner_hilbertShiftSemigroup_left_eq_right n u v)
      x y

end LinearMarkovTwoSidedIntegerPathOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
