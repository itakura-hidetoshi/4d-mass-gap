import MGAP4D.MathlibAnalytic.FiniteOrientedFourDimensionalPlaquetteGeometry
import MGAP4D.MathlibAnalytic.PeriodicHypercubicPlaquetteIncidence

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

def periodicOrientationToFinite :
    PeriodicHypercubicOrientation → FiniteBoundaryOrientation
  | .forward => .forward
  | .backward => .backward

def periodicBoundaryStepToFinite
    {n : ℕ} (s : PeriodicHypercubicBoundaryStep n) :
    FiniteOrientedBoundaryStep (PeriodicHypercubicEdge n) :=
  ⟨s.edge, periodicOrientationToFinite s.orientation⟩

end

end MathlibAnalytic
end MGAP4D
