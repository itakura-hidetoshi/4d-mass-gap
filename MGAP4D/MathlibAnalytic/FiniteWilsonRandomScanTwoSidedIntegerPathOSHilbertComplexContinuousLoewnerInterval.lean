import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertComplexContinuousPositiveContractionSemigroup
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertComplexContinuousLoewnerInterval

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped ComplexOrder

/-- Every actual finite Wilson natural-time complex temporal OS quadratic form
is bounded above by that of the identity. -/
theorem FiniteLatticeWilsonSystem.re_inner_randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap_self_le
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (x : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) :
    (inner ℂ
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n x)
      x).re ≤ (inner ℂ x x).re :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.re_inner_hilbertShiftSemigroupComplexContinuousLinearMap_self_le
    n x

/-- The complement of every actual finite Wilson natural-time complex temporal
OS operator is positive. -/
theorem FiniteLatticeWilsonSystem.one_sub_randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap_isPositive
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    ((1 : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification →L[ℂ]
        L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) -
      L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n).IsPositive :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.one_sub_hilbertShiftSemigroupComplexContinuousLinearMap_isPositive
    n

/-- Every actual finite Wilson natural-time complex temporal OS operator is at
most the identity. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap_le_one
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n ≤ 1 :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupComplexContinuousLinearMap_le_one
    n

/-- Every actual finite Wilson natural-time complex temporal OS operator belongs
to the Loewner interval `[0, I]`. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap_mem_Icc
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n ∈
      Set.Icc
        (0 : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification →L[ℂ]
          L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification)
        1 :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupComplexContinuousLinearMap_mem_Icc
    (finite_lattice_randomScanTransitionQuadraticNonnegative L) n

/-- The actual finite Wilson one-step complex temporal OS quadratic form is
bounded above by that of the identity. -/
theorem FiniteLatticeWilsonSystem.re_inner_randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap_self_le
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (x : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) :
    (inner ℂ
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap x)
      x).re ≤ (inner ℂ x x).re :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.re_inner_hilbertShiftComplexContinuousLinearMap_self_le
    x

/-- The complement of the actual finite Wilson one-step complex temporal OS
shift is positive. -/
theorem FiniteLatticeWilsonSystem.one_sub_randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap_isPositive
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    ((1 : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification →L[ℂ]
        L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) -
      L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap).IsPositive :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.one_sub_hilbertShiftComplexContinuousLinearMap_isPositive

/-- The actual finite Wilson one-step complex temporal OS shift is at most the
identity. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap_le_one
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap ≤ 1 :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftComplexContinuousLinearMap_le_one

/-- The actual finite Wilson one-step complex temporal OS shift belongs to the
Loewner interval `[0, I]`. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap_mem_Icc
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap ∈
      Set.Icc
        (0 : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification →L[ℂ]
          L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification)
        1 :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftComplexContinuousLinearMap_mem_Icc
    (finite_lattice_randomScanTransitionQuadraticNonnegative L)

end

end MathlibAnalytic
end MGAP4D
