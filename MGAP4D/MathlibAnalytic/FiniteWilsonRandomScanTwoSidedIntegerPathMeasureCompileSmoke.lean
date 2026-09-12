import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathMeasure

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

#check finite_lattice_randomScanIntegerFiniteMarginalMeasure_projective
#check finite_lattice_randomScanTwoSidedIntegerPathMeasure_isProjectiveLimit

example (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    IsProbabilityMeasure L.randomScanTwoSidedIntegerPathMeasure := by
  infer_instance

end MathlibAnalytic
end MGAP4D
