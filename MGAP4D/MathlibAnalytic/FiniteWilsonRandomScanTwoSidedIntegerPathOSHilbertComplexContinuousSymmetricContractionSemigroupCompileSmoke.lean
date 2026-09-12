import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertComplexContinuousSymmetricContractionSemigroup

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable (L : FiniteLatticeWilsonSystem) [Nonempty L.Edge]

example
    (x y : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) :
    inner ℂ
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap x) y =
      inner ℂ x
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap y) :=
  L.inner_randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap_left_eq_right x y

example
    (n : ℕ)
    (x y : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) :
    inner ℂ
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n x) y =
      inner ℂ x
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n y) :=
  L.inner_randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap_left_eq_right n x y

end

end MathlibAnalytic
end MGAP4D
