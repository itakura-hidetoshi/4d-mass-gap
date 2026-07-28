import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSPreHilbert

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (F G : linearMarkovPositiveTimeCylinderSubalgebra
      (Ω := L.Configuration)) :
    inner ℝ
        (L.randomScanTwoSidedIntegerPathOSClass F)
        (L.randomScanTwoSidedIntegerPathOSClass G) =
      L.randomScanTwoSidedIntegerPathOSForm F G :=
  L.inner_randomScanTwoSidedIntegerPathOSClass F G

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (F : linearMarkovPositiveTimeCylinderSubalgebra
      (Ω := L.Configuration)) :
    L.randomScanTwoSidedIntegerPathOSClass F = 0 ↔
      F ∈ L.randomScanTwoSidedIntegerPathOSNull :=
  L.randomScanTwoSidedIntegerPathOSClass_eq_zero_iff F

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (F G : linearMarkovPositiveTimeCylinderSubalgebra
      (Ω := L.Configuration)) :
    L.randomScanTwoSidedIntegerPathOSClass F =
        L.randomScanTwoSidedIntegerPathOSClass G ↔
      F - G ∈ L.randomScanTwoSidedIntegerPathOSNull :=
  L.randomScanTwoSidedIntegerPathOSClass_eq_class_iff F G

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (x : L.RandomScanTwoSidedIntegerPathOSPreHilbert) :
    inner ℝ x x = 0 ↔ x = 0 :=
  L.randomScanTwoSidedIntegerPathOSPreHilbert_inner_self_eq_zero_iff x

end

end MathlibAnalytic
end MGAP4D
