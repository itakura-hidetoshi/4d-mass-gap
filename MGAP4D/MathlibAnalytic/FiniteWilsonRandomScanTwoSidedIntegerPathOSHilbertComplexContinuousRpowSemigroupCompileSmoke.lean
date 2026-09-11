import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertComplexContinuousRpowSemigroup

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped ComplexOrder NNReal

namespace ComplexContinuousPositiveContraction

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

example
    (T : H →L[ℂ] H)
    (x y : ℝ)
    (hunit : IsUnit T) :
    rpow T (x + y) = rpow T x * rpow T y :=
  rpow_add_of_isUnit T x y hunit

end ComplexContinuousPositiveContraction

variable (L : FiniteLatticeWilsonSystem) [Nonempty L.Edge]

example (n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow n 0 = 1 :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow_zero n

example (n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow n 1 =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow_one n

example (n m : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow n (m : ℝ) =
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n) ^ m :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow_natCast n m

example (n : ℕ) (p : ℝ≥0) (hp : 0 < p) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow n (p : ℝ) =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow n p :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow_coe_eq_NNRpow
    n p hp

example (n : ℕ) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ComplexContinuousPositiveContraction.rpow
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow n x) y =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow n (x * y) :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow_rpow_of_exponent_nonneg
    n x y hx hy

example (n : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow n x ∈
      Set.Icc
        (0 : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification →L[ℂ]
          L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification)
        1 :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow_mem_Icc
    n x hx

example (n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow (2 * n) (1 / 2 : ℝ) =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow_one_div_two_two_mul_eq n

example :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow 2 (1 / 2 : ℝ) =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow_one_div_two_two_eq_shift

end

end MathlibAnalytic
end MGAP4D
