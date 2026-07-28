import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertCompletion

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (F G : linearMarkovPositiveTimeCylinderSubalgebra
      (Ω := L.Configuration)) :
    inner ℝ
        (L.randomScanTwoSidedIntegerPathOSHilbertClass F)
        (L.randomScanTwoSidedIntegerPathOSHilbertClass G) =
      L.randomScanTwoSidedIntegerPathOSForm F G :=
  L.inner_randomScanTwoSidedIntegerPathOSHilbertClass F G

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    DenseRange L.randomScanTwoSidedIntegerPathOSPreHilbertToHilbert :=
  L.randomScanTwoSidedIntegerPathOSPreHilbert_dense

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (x : L.RandomScanTwoSidedIntegerPathOSHilbert) :
    inner ℝ x x = 0 ↔ x = 0 :=
  L.randomScanTwoSidedIntegerPathOSHilbert_inner_self_eq_zero_iff x

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    CompleteSpace L.RandomScanTwoSidedIntegerPathOSHilbert :=
  L.randomScanTwoSidedIntegerPathOSHilbert_complete

end

end MathlibAnalytic
end MGAP4D
