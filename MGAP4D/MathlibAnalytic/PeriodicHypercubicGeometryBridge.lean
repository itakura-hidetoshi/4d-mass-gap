import MGAP4D.MathlibAnalytic.FiniteOrientedFourDimensionalPlaquetteGeometry
import MGAP4D.MathlibAnalytic.PeriodicHypercubicPlaquetteIncidence

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

def periodicOrientationToFinite :
    PeriodicHypercubicOrientation → FiniteBoundaryOrientation
  | .forward => .forward
  | .backward => .backward

end

end MathlibAnalytic
end MGAP4D
