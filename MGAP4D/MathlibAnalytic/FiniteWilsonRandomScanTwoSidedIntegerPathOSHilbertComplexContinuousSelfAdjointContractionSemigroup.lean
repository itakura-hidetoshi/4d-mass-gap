import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertComplexContinuousSymmetricContractionSemigroup
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertComplexContinuousSelfAdjointContractionSemigroup

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The actual finite Wilson continuous complexified one-step temporal OS shift
is symmetric in Mathlib's bundled sense. -/
theorem FiniteLatticeWilsonSystem.isSymmetric_randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap.IsSymmetric :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.isSymmetric_hilbertShiftComplexContinuousLinearMap

/-- The adjoint of the actual finite Wilson continuous complexified one-step
temporal OS shift is the shift itself. -/
theorem FiniteLatticeWilsonSystem.adjoint_randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap_eq_self
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    ContinuousLinearMap.adjoint
        L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.adjoint_hilbertShiftComplexContinuousLinearMap_eq_self

/-- The actual finite Wilson continuous complexified one-step temporal OS shift
is self-adjoint. -/
theorem FiniteLatticeWilsonSystem.isSelfAdjoint_randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    IsSelfAdjoint
      L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.isSelfAdjoint_hilbertShiftComplexContinuousLinearMap

/-- Every actual finite Wilson natural-time continuous complex temporal OS
operator is symmetric in Mathlib's bundled sense. -/
theorem FiniteLatticeWilsonSystem.isSymmetric_randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n).IsSymmetric :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.isSymmetric_hilbertShiftSemigroupComplexContinuousLinearMap n

/-- The adjoint of every actual finite Wilson natural-time continuous complex
temporal OS operator is the operator itself. -/
theorem FiniteLatticeWilsonSystem.adjoint_randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap_eq_self
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    ContinuousLinearMap.adjoint
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n) =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.adjoint_hilbertShiftSemigroupComplexContinuousLinearMap_eq_self n

/-- Every actual finite Wilson natural-time continuous complex temporal OS
operator is self-adjoint. -/
theorem FiniteLatticeWilsonSystem.isSelfAdjoint_randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    IsSelfAdjoint
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n) :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.isSelfAdjoint_hilbertShiftSemigroupComplexContinuousLinearMap n

end

end MathlibAnalytic
end MGAP4D
