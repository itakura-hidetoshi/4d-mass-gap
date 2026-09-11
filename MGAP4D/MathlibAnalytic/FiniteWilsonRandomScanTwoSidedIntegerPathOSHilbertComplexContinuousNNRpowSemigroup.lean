import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertComplexContinuousSquareRootSemigroup
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertComplexContinuousNNRpowSemigroup

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped ComplexOrder NNReal

/-- The CFC nonnegative power of an actual finite Wilson natural-time complex
temporal OS operator. -/
noncomputable def FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (p : ℝ≥0) :
    L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification →L[ℂ]
      L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupComplexContinuousNNRpow
    n p

/-- Every actual finite Wilson temporal OS CFC nonnegative power is
nonnegative. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow_nonneg
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (p : ℝ≥0) :
    0 ≤ L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow n p :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupComplexContinuousNNRpow_nonneg
    n p

/-- Every actual finite Wilson temporal OS CFC nonnegative power is positive. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow_isPositive
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (p : ℝ≥0) :
    (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow n p).IsPositive :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupComplexContinuousNNRpow_isPositive
    n p

/-- Every actual finite Wilson temporal OS CFC nonnegative power is
self-adjoint. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow_isSelfAdjoint
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (p : ℝ≥0) :
    IsSelfAdjoint
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow n p) :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupComplexContinuousNNRpow_isSelfAdjoint
    n p

/-- Exponent zero follows the non-unital CFC convention and gives zero. -/
@[simp]
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow_zero
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow n 0 = 0 :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupComplexContinuousNNRpow_zero
    n

/-- Exponent one recovers the actual finite Wilson natural-time operator. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow_one
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow n 1 =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupComplexContinuousNNRpow_one
    (finite_lattice_randomScanTransitionQuadraticNonnegative L) n

/-- Positive exponents add under multiplication for every actual finite Wilson
natural-time operator. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow_add
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    {p q : ℝ≥0}
    (hp : 0 < p)
    (hq : 0 < q) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow n (p + q) =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow n p *
        L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow n q :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupComplexContinuousNNRpow_add
    n hp hq

/-- Iterated actual finite Wilson CFC nonnegative powers multiply their
exponents. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow_nnrpow
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (p q : ℝ≥0) :
    ComplexContinuousPositiveContraction.nnrpow
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow n p) q =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow n (p * q) :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupComplexContinuousNNRpow_nnrpow
    n p q

/-- For exponents in `[0,1]`, every actual finite Wilson temporal OS
nonnegative power is at most the identity. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow_le_one
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (p : ℝ≥0)
    (hp : p ∈ Set.Icc (0 : ℝ≥0) 1) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow n p ≤ 1 :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupComplexContinuousNNRpow_le_one
    n p hp

/-- For exponents in `[0,1]`, every actual finite Wilson temporal OS
nonnegative power belongs to `[0,I]`. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow_mem_Icc
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (p : ℝ≥0)
    (hp : p ∈ Set.Icc (0 : ℝ≥0) 1) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow n p ∈
      Set.Icc
        (0 : L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification →L[ℂ]
          L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification)
        1 :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupComplexContinuousNNRpow_mem_Icc
    n p hp

/-- The exponent `1 / 2` actual finite Wilson nonnegative power is the
canonical square root from the preceding layer. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow_one_div_two_eq_squareRoot
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow n (1 / 2 : ℝ≥0) =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousSquareRoot n :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupComplexContinuousNNRpow_one_div_two_eq_squareRoot
    n

/-- The half-power of the actual finite Wilson time-`2n` operator is the
time-`n` operator. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow_one_div_two_two_mul_eq
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow (2 * n) (1 / 2 : ℝ≥0) =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousLinearMap n :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupComplexContinuousNNRpow_one_div_two_two_mul_eq
    (finite_lattice_randomScanTransitionQuadraticNonnegative L) n

/-- The half-power of the actual finite Wilson two-step operator is the
one-step shift. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow_one_div_two_two_eq_shift
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupComplexContinuousNNRpow 2 (1 / 2 : ℝ≥0) =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftComplexContinuousLinearMap :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupComplexContinuousNNRpow_one_div_two_two_eq_shift
    (finite_lattice_randomScanTransitionQuadraticNonnegative L)

end

end MathlibAnalytic
end MGAP4D
