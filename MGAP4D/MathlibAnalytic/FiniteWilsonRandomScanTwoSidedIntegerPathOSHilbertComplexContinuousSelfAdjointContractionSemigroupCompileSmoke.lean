import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertComplexContinuousSelfAdjointContractionSemigroup

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable (L : FiniteLatticeWilsonSystem) [Nonempty L.Edge]

example :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap.IsSymmetric :=
  L.isSymmetric_randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap

example :
    ContinuousLinearMap.adjoint
        L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap :=
  L.adjoint_randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap_eq_self

example :
    IsSelfAdjoint
      L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap :=
  L.isSelfAdjoint_randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap

example (n : ℕ) :
    (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n).IsSymmetric :=
  L.isSymmetric_randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n

example (n : ℕ) :
    ContinuousLinearMap.adjoint
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n) =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n :=
  L.adjoint_randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap_eq_self n

example (n : ℕ) :
    IsSelfAdjoint
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n) :=
  L.isSelfAdjoint_randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n

end

end MathlibAnalytic
end MGAP4D
