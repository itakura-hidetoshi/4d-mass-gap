import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertComplexContinuousLoewnerInterval

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped ComplexOrder

variable (L : FiniteLatticeWilsonSystem) [Nonempty L.Edge]

example
    (x : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) :
    (inner ℂ
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap x)
      x).re ≤ (inner ℂ x x).re :=
  L.re_inner_randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap_self_le x

example :
    ((1 : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification →L[ℂ]
        L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) -
      L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap).IsPositive :=
  L.one_sub_randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap_isPositive

example :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap ≤ 1 :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap_le_one

example :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap ∈
      Set.Icc
        (0 : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification →L[ℂ]
          L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification)
        1 :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap_mem_Icc

example (n : ℕ)
    (x : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) :
    (inner ℂ
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n x)
      x).re ≤ (inner ℂ x x).re :=
  L.re_inner_randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap_self_le n x

example (n : ℕ) :
    ((1 : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification →L[ℂ]
        L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) -
      L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n).IsPositive :=
  L.one_sub_randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap_isPositive n

example (n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n ≤ 1 :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap_le_one n

example (n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n ∈
      Set.Icc
        (0 : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification →L[ℂ]
          L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification)
        1 :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap_mem_Icc n

end

end MathlibAnalytic
end MGAP4D
