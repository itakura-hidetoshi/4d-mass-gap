import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertShift
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertShiftSemigroup

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The discrete temporal OS transfer semigroup of the actual finite Wilson
Gibbs-stationary random-scan system. -/
noncomputable def FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    L.RandomScanTwoSidedIntegerPathOSHilbert →L[ℝ]
      L.RandomScanTwoSidedIntegerPathOSHilbert :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroup n

@[simp] theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_zero
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup 0 = 1 :=
  rfl

@[simp] theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_succ
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup (n + 1) =
      L.randomScanTwoSidedIntegerPathOSHilbertShift.comp
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n) :=
  rfl

/-- The actual finite Wilson completed shifts satisfy the additive semigroup law. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_add
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (m n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup (m + n) =
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup m).comp
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n) :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroup_add m n

/-- Every actual finite Wilson discrete-time transfer operator is norm
nonincreasing. -/
theorem FiniteLatticeWilsonSystem.norm_randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_le
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (x : L.RandomScanTwoSidedIntegerPathOSHilbert) :
    ‖L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n x‖ ≤ ‖x‖ :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.norm_hilbertShiftSemigroup_le n x

/-- On completed actual Wilson observable classes, the semigroup is repeated
positive-time translation. -/
@[simp] theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_class
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (F : linearMarkovPositiveTimeCylinderSubalgebra
      (Ω := L.Configuration)) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n
        (L.randomScanTwoSidedIntegerPathOSHilbertClass F) =
      L.randomScanTwoSidedIntegerPathOSHilbertClass
        (linearMarkovPositiveTimeShiftIterate n F) :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroup_completedObservableClass
    n F

end

end MathlibAnalytic
end MGAP4D
