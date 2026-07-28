import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertComplexInnerPrecursor

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

example (L : FiniteLatticeWilsonSystem) [Nonempty L.Edge]
    (x : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) :
    L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexificationImaginaryUnitLinearIsometry
        (L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexificationImaginaryUnitLinearIsometry x) =
      -x :=
  RealTensorComplexification.imaginaryUnitLinearIsometry_sq_apply x

example (L : FiniteLatticeWilsonSystem) [Nonempty L.Edge]
    (x : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) :
    L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexificationComplexInner x x =
      (RealTensorComplexification.realInner x x : ℂ) :=
  L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexificationComplexInner_self x

example (L : FiniteLatticeWilsonSystem) [Nonempty L.Edge]
    (n : ℕ)
    (x : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification n
        (L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexificationImaginaryUnitLinearIsometry x) =
      L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexificationImaginaryUnitLinearIsometry
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification n x) :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification_map_imaginaryUnit n x

end

end MathlibAnalytic
end MGAP4D
