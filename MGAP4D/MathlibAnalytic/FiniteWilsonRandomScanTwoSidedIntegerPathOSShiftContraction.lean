import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSShift
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSShiftContraction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The actual finite Wilson positive-time shift as a contractive continuous
real-linear endomorphism of the separated temporal OS pre-Hilbert space. -/
noncomputable def FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSShiftContinuousLinearMap
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    L.RandomScanTwoSidedIntegerPathOSPreHilbert →L[ℝ]
      L.RandomScanTwoSidedIntegerPathOSPreHilbert :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData
    .separatedShiftContinuousLinearMap

/-- The actual finite Wilson temporal shift is norm nonincreasing. -/
theorem FiniteLatticeWilsonSystem.norm_randomScanTwoSidedIntegerPathOSShift_le
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (x : L.RandomScanTwoSidedIntegerPathOSPreHilbert) :
    ‖L.randomScanTwoSidedIntegerPathOSShiftContinuousLinearMap x‖ ≤ ‖x‖ := by
  exact
    L.randomScanTwoSidedIntegerPathOSPreHilbertData
      .norm_separatedShiftLinearMap_le x

/-- The continuous actual Wilson shift sends an observable class to the class of
its positive-time translate. -/
@[simp] theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSShiftContinuousLinearMap_class
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (F : linearMarkovPositiveTimeCylinderSubalgebra
      (Ω := L.Configuration)) :
    L.randomScanTwoSidedIntegerPathOSShiftContinuousLinearMap
        (L.randomScanTwoSidedIntegerPathOSClass F) =
      L.randomScanTwoSidedIntegerPathOSClass
        (linearMarkovPositiveTimeShiftAlgHom F) := by
  exact
    LinearMarkovTwoSidedIntegerPathOSPreHilbertData
      .separatedShiftContinuousLinearMap_observableClass
        L.randomScanTwoSidedIntegerPathOSPreHilbertData F

/-- The continuous actual Wilson temporal shift remains symmetric for the
separated OS inner product. -/
theorem FiniteLatticeWilsonSystem.inner_randomScanTwoSidedIntegerPathOSShiftContinuous_left_eq_right
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (x y : L.RandomScanTwoSidedIntegerPathOSPreHilbert) :
    inner ℝ
        (L.randomScanTwoSidedIntegerPathOSShiftContinuousLinearMap x) y =
      inner ℝ x
        (L.randomScanTwoSidedIntegerPathOSShiftContinuousLinearMap y) := by
  exact
    LinearMarkovTwoSidedIntegerPathOSPreHilbertData
      .inner_separatedShiftContinuousLinearMap_left_eq_right
        L.randomScanTwoSidedIntegerPathOSPreHilbertData x y

end

end MathlibAnalytic
end MGAP4D
