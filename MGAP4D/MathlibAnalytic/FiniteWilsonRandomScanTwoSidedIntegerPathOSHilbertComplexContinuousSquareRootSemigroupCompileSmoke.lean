import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertComplexContinuousSquareRootSemigroup

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped ComplexOrder

variable (L : FiniteLatticeWilsonSystem) [Nonempty L.Edge]

example (n : ℕ) :
    0 ≤ L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousSquareRoot n :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousSquareRoot_nonneg n

example (n : ℕ) :
    (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousSquareRoot n).IsPositive :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousSquareRoot_isPositive n

example (n : ℕ) :
    IsSelfAdjoint
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousSquareRoot n) :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousSquareRoot_isSelfAdjoint n

example (n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousSquareRoot n *
        L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousSquareRoot n =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousSquareRoot_mul_self_eq n

example (n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousSquareRoot n ≤ 1 :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousSquareRoot_le_one n

example (n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousSquareRoot n ∈
      Set.Icc
        (0 : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification →L[ℂ]
          L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification)
        1 :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousSquareRoot_mem_Icc n

example (n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousSquareRoot (2 * n) =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousSquareRoot_two_mul_eq n

example :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousSquareRoot 2 =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousSquareRoot_two_eq_shift

end

end MathlibAnalytic
end MGAP4D
