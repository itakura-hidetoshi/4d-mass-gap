import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertComplexContinuousPositiveContractionSemigroup

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped ComplexOrder

variable (L : FiniteLatticeWilsonSystem) [Nonempty L.Edge]

example
    (x : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) :
    0 ≤ (inner ℂ
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap x)
      x).re :=
  L.re_inner_randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap_self_nonneg x

example :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap.IsPositive :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap_isPositive

example :
    0 ≤ L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap_nonneg

example
    (x : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) :
    0 ≤ inner ℂ
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap x)
      x :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap_isPositive.inner_nonneg_left x

example (n : ℕ)
    (x : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) :
    0 ≤ (inner ℂ
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n x)
      x).re :=
  L.re_inner_randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap_self_nonneg n x

example (n : ℕ) :
    (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n).IsPositive :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap_isPositive n

example (n : ℕ) :
    0 ≤ L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap_nonneg n

example (n : ℕ)
    (x : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) :
    0 ≤ inner ℂ
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n x)
      x :=
  (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap_isPositive n).inner_nonneg_left x

end

end MathlibAnalytic
end MGAP4D
