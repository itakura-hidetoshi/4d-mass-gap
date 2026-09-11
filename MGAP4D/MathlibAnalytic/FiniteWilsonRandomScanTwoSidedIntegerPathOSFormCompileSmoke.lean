import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSForm

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (F G : linearMarkovPositiveTimeCylinderSubalgebra
      (Ω := L.Configuration)) :
    L.randomScanTwoSidedIntegerPathOSForm F G =
      L.randomScanTwoSidedIntegerPathOSForm G F :=
  finite_lattice_randomScanTwoSidedIntegerPathOSForm_symmetric L F G

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (F G : linearMarkovPositiveTimeCylinderSubalgebra
      (Ω := L.Configuration)) :
    (L.randomScanTwoSidedIntegerPathOSForm F G) ^ 2 ≤
      L.randomScanTwoSidedIntegerPathOSForm F F *
        L.randomScanTwoSidedIntegerPathOSForm G G :=
  finite_lattice_randomScanTwoSidedIntegerPathOSForm_cauchy_schwarz L F G

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (F : linearMarkovPositiveTimeCylinderSubalgebra
      (Ω := L.Configuration)) :
    F ∈ L.randomScanTwoSidedIntegerPathOSNull ↔
      ∀ G : linearMarkovPositiveTimeCylinderSubalgebra
          (Ω := L.Configuration),
        L.randomScanTwoSidedIntegerPathOSForm F G = 0 :=
  L.mem_randomScanTwoSidedIntegerPathOSNull_iff_forall_orthogonal F

end

end MathlibAnalytic
end MGAP4D
