import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertComplexContinuousNNRpowSemigroup

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped ComplexOrder NNReal

variable (L : FiniteLatticeWilsonSystem)
  [Nonempty L.Edge]

example (n : ℕ) (p : ℝ≥0) :
    0 ≤ L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow n p :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow_nonneg
    n p

example (n : ℕ) (p : ℝ≥0) :
    (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow n p).IsPositive :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow_isPositive
    n p

example (n : ℕ) (p : ℝ≥0) :
    IsSelfAdjoint
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow n p) :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow_isSelfAdjoint
    n p

example (n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow n 0 = 0 := by
  simp

example (n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow n 1 =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow_one
    n

example (n : ℕ) {p q : ℝ≥0} (hp : 0 < p) (hq : 0 < q) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow n (p + q) =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow n p *
        L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow n q :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow_add
    n hp hq

example (n : ℕ) (p q : ℝ≥0) :
    ComplexContinuousPositiveContraction.nnrpow
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow n p) q =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow n (p * q) :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow_nnrpow
    n p q

example (n : ℕ) (p : ℝ≥0) (hp : p ∈ Set.Icc (0 : ℝ≥0) 1) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow n p ∈
      Set.Icc
        (0 : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification →L[ℂ]
          L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification)
        1 :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow_mem_Icc
    n p hp

example (n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow n (1 / 2 : ℝ≥0) =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousSquareRoot n :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow_one_div_two_eq_squareRoot
    n

example (n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow (2 * n) (1 / 2 : ℝ≥0) =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow_one_div_two_two_mul_eq
    n

example :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow 2 (1 / 2 : ℝ≥0) =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow_one_div_two_two_eq_shift

end

end MathlibAnalytic
end MGAP4D
