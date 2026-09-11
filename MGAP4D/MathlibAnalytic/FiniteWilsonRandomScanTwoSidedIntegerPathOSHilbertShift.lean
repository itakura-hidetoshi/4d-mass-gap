import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertCompletion
import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSShiftContraction
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertShift

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The actual finite Wilson temporal OS shift on the completed Hilbert space. -/
noncomputable def FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShift
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    L.RandomScanTwoSidedIntegerPathOSHilbert →L[ℝ]
      L.RandomScanTwoSidedIntegerPathOSHilbert :=
  LinearMarkovTwoSidedIntegerPathOSPreHilbertData.hilbertShiftContinuousLinearMap
    L.randomScanTwoSidedIntegerPathOSPreHilbertData

/-- The completed actual Wilson shift agrees with the separated shift on the
 canonical dense embedding. -/
@[simp] theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShift_preHilbert
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (x : L.RandomScanTwoSidedIntegerPathOSPreHilbert) :
    L.randomScanTwoSidedIntegerPathOSHilbertShift
        (L.randomScanTwoSidedIntegerPathOSPreHilbertToHilbert x) =
      L.randomScanTwoSidedIntegerPathOSPreHilbertToHilbert
        (L.randomScanTwoSidedIntegerPathOSShiftContinuousLinearMap x) := by
  exact
    LinearMarkovTwoSidedIntegerPathOSPreHilbertData.hilbertShiftContinuousLinearMap_completedClass
      L.randomScanTwoSidedIntegerPathOSPreHilbertData x

/-- On completed actual Wilson observable classes, the Hilbert shift is positive-time
 translation. -/
@[simp] theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShift_class
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (F : linearMarkovPositiveTimeCylinderSubalgebra
      (Ω := L.Configuration)) :
    L.randomScanTwoSidedIntegerPathOSHilbertShift
        (L.randomScanTwoSidedIntegerPathOSHilbertClass F) =
      L.randomScanTwoSidedIntegerPathOSHilbertClass
        (linearMarkovPositiveTimeShiftAlgHom F) := by
  exact
    LinearMarkovTwoSidedIntegerPathOSPreHilbertData.hilbertShiftContinuousLinearMap_completedObservableClass
      L.randomScanTwoSidedIntegerPathOSPreHilbertData F

/-- The completed actual Wilson temporal shift is norm nonincreasing. -/
theorem FiniteLatticeWilsonSystem.norm_randomScanTwoSidedIntegerPathOSHilbertShift_le
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (x : L.RandomScanTwoSidedIntegerPathOSHilbert) :
    ‖L.randomScanTwoSidedIntegerPathOSHilbertShift x‖ ≤ ‖x‖ :=
  LinearMarkovTwoSidedIntegerPathOSPreHilbertData.norm_hilbertShiftContinuousLinearMap_le
    L.randomScanTwoSidedIntegerPathOSPreHilbertData x

/-- The completed actual Wilson temporal shift is symmetric. -/
theorem FiniteLatticeWilsonSystem.inner_randomScanTwoSidedIntegerPathOSHilbertShift_left_eq_right
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (x y : L.RandomScanTwoSidedIntegerPathOSHilbert) :
    inner ℝ (L.randomScanTwoSidedIntegerPathOSHilbertShift x) y =
      inner ℝ x (L.randomScanTwoSidedIntegerPathOSHilbertShift y) :=
  LinearMarkovTwoSidedIntegerPathOSPreHilbertData.inner_hilbertShiftContinuousLinearMap_left_eq_right
    L.randomScanTwoSidedIntegerPathOSPreHilbertData x y

end

end MathlibAnalytic
end MGAP4D
