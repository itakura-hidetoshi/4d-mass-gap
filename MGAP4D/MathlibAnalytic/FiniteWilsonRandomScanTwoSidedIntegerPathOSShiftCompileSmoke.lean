import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSShift

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (F : linearMarkovPositiveTimeCylinderSubalgebra
      (Ω := L.Configuration)) :
    L.randomScanTwoSidedIntegerPathOSShiftLinearMap
        (L.randomScanTwoSidedIntegerPathOSClass F) =
      L.randomScanTwoSidedIntegerPathOSClass
        (linearMarkovPositiveTimeShiftAlgHom F) :=
  L.randomScanTwoSidedIntegerPathOSShiftLinearMap_class F

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (F : linearMarkovPositiveTimeCylinderSubalgebra
      (Ω := L.Configuration))
    (hF : F ∈ L.randomScanTwoSidedIntegerPathOSNull) :
    linearMarkovPositiveTimeShiftAlgHom F ∈
      L.randomScanTwoSidedIntegerPathOSNull :=
  L.randomScanTwoSidedIntegerPathOSNull_shift F hF

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (x y : L.RandomScanTwoSidedIntegerPathOSPreHilbert) :
    inner ℝ (L.randomScanTwoSidedIntegerPathOSShiftLinearMap x) y =
      inner ℝ x (L.randomScanTwoSidedIntegerPathOSShiftLinearMap y) :=
  L.inner_randomScanTwoSidedIntegerPathOSShift_left_eq_right x y

end

end MathlibAnalytic
end MGAP4D
