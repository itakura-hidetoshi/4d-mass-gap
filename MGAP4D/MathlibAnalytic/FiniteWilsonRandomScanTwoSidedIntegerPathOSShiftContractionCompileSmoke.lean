import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSShiftContraction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (x : L.RandomScanTwoSidedIntegerPathOSPreHilbert) :
    ‖L.randomScanTwoSidedIntegerPathOSShiftContinuousLinearMap x‖ ≤ ‖x‖ :=
  L.norm_randomScanTwoSidedIntegerPathOSShift_le x

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (F : linearMarkovPositiveTimeCylinderSubalgebra
      (Ω := L.Configuration)) :
    L.randomScanTwoSidedIntegerPathOSShiftContinuousLinearMap
        (L.randomScanTwoSidedIntegerPathOSClass F) =
      L.randomScanTwoSidedIntegerPathOSClass
        (linearMarkovPositiveTimeShiftAlgHom F) :=
  L.randomScanTwoSidedIntegerPathOSShiftContinuousLinearMap_class F

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (x y : L.RandomScanTwoSidedIntegerPathOSPreHilbert) :
    inner ℝ
        (L.randomScanTwoSidedIntegerPathOSShiftContinuousLinearMap x) y =
      inner ℝ x
        (L.randomScanTwoSidedIntegerPathOSShiftContinuousLinearMap y) :=
  L.inner_randomScanTwoSidedIntegerPathOSShiftContinuous_left_eq_right x y

end

end MathlibAnalytic
end MGAP4D
