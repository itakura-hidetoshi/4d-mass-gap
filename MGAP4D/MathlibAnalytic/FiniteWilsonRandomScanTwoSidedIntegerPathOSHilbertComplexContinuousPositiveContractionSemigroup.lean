import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertPositiveSelfAdjoint
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertComplexContinuousPositiveContractionSemigroup
import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertComplexContinuousSelfAdjointContractionSemigroup

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Every actual finite Wilson natural-time continuous complex temporal OS
operator has nonnegative real quadratic form. -/
theorem FiniteLatticeWilsonSystem.re_inner_randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap_self_nonneg
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (x : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) :
    0 ≤ (inner ℂ
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n x)
      x).re :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.re_inner_hilbertShiftSemigroupComplexContinuousLinearMap_self_nonneg
    (finite_lattice_randomScanTransitionQuadraticNonnegative L) n x

/-- Every actual finite Wilson natural-time continuous complex temporal OS
operator is positive in Mathlib's bundled sense. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap_isPositive
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n).IsPositive :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupComplexContinuousLinearMap_isPositive
    (finite_lattice_randomScanTransitionQuadraticNonnegative L) n

/-- Every actual finite Wilson natural-time continuous complex temporal OS
operator is nonnegative in the Loewner order. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap_nonneg
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    0 ≤ L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupComplexContinuousLinearMap_nonneg
    (finite_lattice_randomScanTransitionQuadraticNonnegative L) n

/-- The actual finite Wilson one-step continuous complex temporal OS shift has
nonnegative real quadratic form. -/
theorem FiniteLatticeWilsonSystem.re_inner_randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap_self_nonneg
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (x : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification) :
    0 ≤ (inner ℂ
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap x)
      x).re :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.re_inner_hilbertShiftComplexContinuousLinearMap_self_nonneg
    (finite_lattice_randomScanTransitionQuadraticNonnegative L) x

/-- The actual finite Wilson one-step continuous complex temporal OS shift is
positive. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap_isPositive
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap.IsPositive :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftComplexContinuousLinearMap_isPositive
    (finite_lattice_randomScanTransitionQuadraticNonnegative L)

/-- The actual finite Wilson one-step continuous complex temporal OS shift is
nonnegative in the Loewner order. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap_nonneg
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    0 ≤ L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftComplexContinuousLinearMap_nonneg
    (finite_lattice_randomScanTransitionQuadraticNonnegative L)

end

end MathlibAnalytic
end MGAP4D
