import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertComplexContinuousContractionSemigroup
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertComplexContinuousSymmetricContractionSemigroup

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The actual finite Wilson continuous complexified one-step temporal OS shift
is symmetric for the canonical complex inner product. -/
theorem FiniteLatticeWilsonSystem.inner_randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap_left_eq_right
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (x y : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) :
    inner ℂ
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap x) y =
      inner ℂ x
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap y) :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.inner_hilbertShiftComplexContinuousLinearMap_left_eq_right x y

/-- Every actual finite Wilson natural-time continuous complex temporal OS
operator is symmetric for the canonical complex inner product. -/
theorem FiniteLatticeWilsonSystem.inner_randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap_left_eq_right
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (x y : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) :
    inner ℂ
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n x) y =
      inner ℂ x
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n y) :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.inner_hilbertShiftSemigroupComplexContinuousLinearMap_left_eq_right n x y

end

end MathlibAnalytic
end MGAP4D
