import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertComplexContinuousNNRpowSemigroup
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertComplexContinuousRpowSemigroup

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped ComplexOrder NNReal

/-- The unital CFC real power of an actual finite Wilson natural-time complex
temporal OS operator. -/
noncomputable def FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (x : ℝ) :
    L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification →L[ℂ]
      L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupComplexContinuousRpow
    n x

/-- Every actual finite Wilson temporal OS unital real power is nonnegative. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow_nonneg
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (x : ℝ) :
    0 ≤ L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow n x :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupComplexContinuousRpow_nonneg
    n x

/-- Every actual finite Wilson temporal OS unital real power is positive. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow_isPositive
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (x : ℝ) :
    (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow n x).IsPositive :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupComplexContinuousRpow_isPositive
    n x

/-- Every actual finite Wilson temporal OS unital real power is self-adjoint. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow_isSelfAdjoint
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (x : ℝ) :
    IsSelfAdjoint
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow n x) :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupComplexContinuousRpow_isSelfAdjoint
    n x

/-- Exponent zero gives the identity for the actual finite Wilson operator. -/
@[simp]
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow_zero
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow n 0 = 1 :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupComplexContinuousRpow_zero
    (finite_lattice_randomScanTransitionQuadraticNonnegative L) n

/-- Exponent one recovers the actual finite Wilson natural-time operator. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow_one
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow n 1 =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupComplexContinuousRpow_one
    (finite_lattice_randomScanTransitionQuadraticNonnegative L) n

/-- Natural-number real exponents agree with ordinary operator powers. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow_natCast
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n m : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow n (m : ℝ) =
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n) ^ m :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupComplexContinuousRpow_natCast
    (finite_lattice_randomScanTransitionQuadraticNonnegative L) n m

/-- Positive real exponents agree with the preceding actual finite Wilson
non-unital nonnegative powers. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow_coe_eq_NNRpow
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (p : ℝ≥0)
    (hp : 0 < p) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow n (p : ℝ) =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow n p :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupComplexContinuousRpow_coe_eq_NNRpow
    n p hp

/-- Iterated actual finite Wilson unital real powers multiply nonnegative
exponents. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow_rpow_of_exponent_nonneg
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (x y : ℝ)
    (hx : 0 ≤ x)
    (hy : 0 ≤ y) :
    ComplexContinuousPositiveContraction.rpow
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow n x) y =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow n (x * y) :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupComplexContinuousRpow_rpow_of_exponent_nonneg
    (finite_lattice_randomScanTransitionQuadraticNonnegative L) n x y hx hy

/-- For exponents in `[0,1]`, every actual finite Wilson unital real power is at
most the identity. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow_le_one
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow n x ≤ 1 :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupComplexContinuousRpow_le_one
    n x hx

/-- For exponents in `[0,1]`, every actual finite Wilson unital real power
belongs to `[0,I]`. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow_mem_Icc
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow n x ∈
      Set.Icc
        (0 : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification →L[ℂ]
          L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification)
        1 :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupComplexContinuousRpow_mem_Icc
    n x hx

/-- The real half-power is the actual finite Wilson canonical square root. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow_one_div_two_eq_squareRoot
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow n (1 / 2 : ℝ) =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousSquareRoot n :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupComplexContinuousRpow_one_div_two_eq_squareRoot
    n

/-- The real half-power of the actual finite Wilson time-`2n` operator is the
time-`n` operator. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow_one_div_two_two_mul_eq
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow (2 * n) (1 / 2 : ℝ) =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupComplexContinuousRpow_one_div_two_two_mul_eq
    (finite_lattice_randomScanTransitionQuadraticNonnegative L) n

/-- The real half-power of the actual finite Wilson two-step operator is the
one-step shift. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow_one_div_two_two_eq_shift
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousRpow 2 (1 / 2 : ℝ) =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupComplexContinuousRpow_one_div_two_two_eq_shift
    (finite_lattice_randomScanTransitionQuadraticNonnegative L)

end

end MathlibAnalytic
end MGAP4D
