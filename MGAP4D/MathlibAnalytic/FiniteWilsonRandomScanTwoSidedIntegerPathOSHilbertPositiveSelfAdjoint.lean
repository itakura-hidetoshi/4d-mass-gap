import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertOddTimePositive
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertPositiveSelfAdjoint

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Every natural-time member of the actual finite Wilson random-scan temporal OS
semigroup has nonnegative quadratic form. -/
theorem FiniteLatticeWilsonSystem.inner_randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_self_nonneg
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (x : L.RandomScanTwoSidedIntegerPathOSHilbert) :
    0 ≤ inner ℝ
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n x) x :=
  LinearMarkovTwoSidedIntegerPathOSPreHilbertData.inner_hilbertShiftSemigroup_self_nonneg
    L.randomScanTwoSidedIntegerPathOSPreHilbertData
    (finite_lattice_randomScanTransitionQuadraticNonnegative L) n x

/-- Every natural-time actual finite Wilson random-scan temporal OS operator is
symmetric. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_isSymmetric
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n :
      L.RandomScanTwoSidedIntegerPathOSHilbert →ₗ[ℝ]
        L.RandomScanTwoSidedIntegerPathOSHilbert).IsSymmetric :=
  LinearMarkovTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroup_isSymmetric
    L.randomScanTwoSidedIntegerPathOSPreHilbertData n

/-- Every natural-time actual finite Wilson random-scan temporal OS operator is
positive in Mathlib's bundled continuous-linear-map sense. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_isPositive
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n).IsPositive :=
  LinearMarkovTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroup_isPositive
    L.randomScanTwoSidedIntegerPathOSPreHilbertData
    (finite_lattice_randomScanTransitionQuadraticNonnegative L) n

/-- Every natural-time actual finite Wilson random-scan temporal OS operator is
nonnegative in Mathlib's Loewner order. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_nonneg
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    0 ≤ L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n :=
  LinearMarkovTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroup_nonneg
    L.randomScanTwoSidedIntegerPathOSPreHilbertData
    (finite_lattice_randomScanTransitionQuadraticNonnegative L) n

/-- Every natural-time actual finite Wilson random-scan temporal OS operator is
self-adjoint. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_isSelfAdjoint
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    IsSelfAdjoint
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n) :=
  LinearMarkovTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroup_isSelfAdjoint
    L.randomScanTwoSidedIntegerPathOSPreHilbertData
    (finite_lattice_randomScanTransitionQuadraticNonnegative L) n

/-- The adjoint of every natural-time actual finite Wilson random-scan temporal OS
operator is the operator itself. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_adjoint_eq
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    ContinuousLinearMap.adjoint
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n) =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n :=
  LinearMarkovTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroup_adjoint_eq
    L.randomScanTwoSidedIntegerPathOSPreHilbertData n

end

end MathlibAnalytic
end MGAP4D
