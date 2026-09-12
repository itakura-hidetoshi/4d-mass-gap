import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertPositiveSelfAdjoint
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertLoewnerRayleighInterval

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Every natural-time actual finite Wilson random-scan temporal OS quadratic
form is bounded above by the ambient squared norm. -/
theorem FiniteLatticeWilsonSystem.inner_randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_self_le
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (x : L.RandomScanTwoSidedIntegerPathOSHilbert) :
    inner ℝ
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n x) x ≤
      inner ℝ x x :=
  LinearMarkovTwoSidedIntegerPathOSPreHilbertData.inner_hilbertShiftSemigroup_self_le
    L.randomScanTwoSidedIntegerPathOSPreHilbertData n x

/-- The complement of every natural-time actual finite Wilson random-scan
 temporal OS operator is positive. -/
theorem FiniteLatticeWilsonSystem.one_sub_randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_isPositive
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    ((1 : L.RandomScanTwoSidedIntegerPathOSHilbert →L[ℝ]
        L.RandomScanTwoSidedIntegerPathOSHilbert) -
      L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n).IsPositive :=
  LinearMarkovTwoSidedIntegerPathOSPreHilbertData.one_sub_hilbertShiftSemigroup_isPositive
    L.randomScanTwoSidedIntegerPathOSPreHilbertData n

/-- Every natural-time actual finite Wilson random-scan temporal OS operator is
at most the identity in Mathlib's Loewner order. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_le_one
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n ≤ 1 :=
  LinearMarkovTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroup_le_one
    L.randomScanTwoSidedIntegerPathOSPreHilbertData n

/-- Every natural-time actual finite Wilson random-scan temporal OS operator
belongs to the Loewner interval `[0, I]`. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_mem_Icc
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n ∈
      Set.Icc
        (0 : L.RandomScanTwoSidedIntegerPathOSHilbert →L[ℝ]
          L.RandomScanTwoSidedIntegerPathOSHilbert)
        1 :=
  LinearMarkovTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroup_mem_Icc
    L.randomScanTwoSidedIntegerPathOSPreHilbertData
    (finite_lattice_randomScanTransitionQuadraticNonnegative L) n

/-- Every natural-time actual finite Wilson random-scan temporal OS Rayleigh
quotient is nonnegative. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_rayleighQuotient_nonneg
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (x : L.RandomScanTwoSidedIntegerPathOSHilbert) :
    0 ≤
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n).rayleighQuotient x :=
  LinearMarkovTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroup_rayleighQuotient_nonneg
    L.randomScanTwoSidedIntegerPathOSPreHilbertData
    (finite_lattice_randomScanTransitionQuadraticNonnegative L) n x

/-- Every natural-time actual finite Wilson random-scan temporal OS Rayleigh
quotient is at most one. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_rayleighQuotient_le_one
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (x : L.RandomScanTwoSidedIntegerPathOSHilbert) :
    (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n).rayleighQuotient x ≤ 1 :=
  LinearMarkovTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroup_rayleighQuotient_le_one
    L.randomScanTwoSidedIntegerPathOSPreHilbertData n x

/-- Every natural-time actual finite Wilson random-scan temporal OS Rayleigh
quotient belongs to `[0, 1]`. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_rayleighQuotient_mem_Icc
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (x : L.RandomScanTwoSidedIntegerPathOSHilbert) :
    (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n).rayleighQuotient x ∈
      Set.Icc (0 : ℝ) 1 :=
  LinearMarkovTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroup_rayleighQuotient_mem_Icc
    L.randomScanTwoSidedIntegerPathOSPreHilbertData
    (finite_lattice_randomScanTransitionQuadraticNonnegative L) n x

end

end MathlibAnalytic
end MGAP4D
