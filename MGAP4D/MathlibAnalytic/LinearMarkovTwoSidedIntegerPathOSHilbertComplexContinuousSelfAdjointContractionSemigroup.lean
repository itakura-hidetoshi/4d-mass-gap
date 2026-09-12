import MGAP4D.MathlibAnalytic.RealTensorComplexificationContinuousSelfAdjointContraction
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertComplexContinuousSymmetricContractionSemigroup

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace LinearMarkovTwoSidedIntegerPathOSPreHilbertData

variable {Ω : Type*} [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- The continuous complexified one-step temporal OS shift is symmetric in
Mathlib's bundled sense. -/
theorem isSymmetric_hilbertShiftComplexContinuousLinearMap
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω) :
    D.hilbertShiftComplexContinuousLinearMap.IsSymmetric := by
  intro x y
  exact D.inner_hilbertShiftComplexContinuousLinearMap_left_eq_right x y

/-- The adjoint of the continuous complexified one-step temporal OS shift is the
shift itself. -/
theorem adjoint_hilbertShiftComplexContinuousLinearMap_eq_self
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω) :
    ContinuousLinearMap.adjoint D.hilbertShiftComplexContinuousLinearMap =
      D.hilbertShiftComplexContinuousLinearMap :=
  D.isSymmetric_hilbertShiftComplexContinuousLinearMap.clm_adjoint_eq

/-- The continuous complexified one-step temporal OS shift is self-adjoint. -/
theorem isSelfAdjoint_hilbertShiftComplexContinuousLinearMap
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω) :
    IsSelfAdjoint D.hilbertShiftComplexContinuousLinearMap :=
  D.isSymmetric_hilbertShiftComplexContinuousLinearMap.isSelfAdjoint

/-- Every natural-time member of the continuous complex temporal OS semigroup is
symmetric in Mathlib's bundled sense. -/
theorem isSymmetric_hilbertShiftSemigroupComplexContinuousLinearMap
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ) :
    (D.hilbertShiftSemigroupComplexContinuousLinearMap n).IsSymmetric := by
  intro x y
  exact D.inner_hilbertShiftSemigroupComplexContinuousLinearMap_left_eq_right
    n x y

/-- The adjoint of every natural-time continuous complex temporal OS operator is
the operator itself. -/
theorem adjoint_hilbertShiftSemigroupComplexContinuousLinearMap_eq_self
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ) :
    ContinuousLinearMap.adjoint
        (D.hilbertShiftSemigroupComplexContinuousLinearMap n) =
      D.hilbertShiftSemigroupComplexContinuousLinearMap n :=
  (D.isSymmetric_hilbertShiftSemigroupComplexContinuousLinearMap n).clm_adjoint_eq

/-- Every natural-time member of the continuous complex temporal OS semigroup is
self-adjoint. -/
theorem isSelfAdjoint_hilbertShiftSemigroupComplexContinuousLinearMap
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ) :
    IsSelfAdjoint (D.hilbertShiftSemigroupComplexContinuousLinearMap n) :=
  (D.isSymmetric_hilbertShiftSemigroupComplexContinuousLinearMap n).isSelfAdjoint

end LinearMarkovTwoSidedIntegerPathOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
