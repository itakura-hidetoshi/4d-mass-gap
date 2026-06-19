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

@[simp]
theorem periodicBoundaryStepToFinite_initial
    {n : ℕ} (s : PeriodicHypercubicBoundaryStep n) :
    (periodicBoundaryStepToFinite s).initial
        (periodicHypercubicEdgeSource n)
        (periodicHypercubicEdgeTarget n) = s.source := by
  cases s with
  | mk edge orientation => cases orientation <;> rfl

end

end MathlibAnalytic
end MGAP4D
