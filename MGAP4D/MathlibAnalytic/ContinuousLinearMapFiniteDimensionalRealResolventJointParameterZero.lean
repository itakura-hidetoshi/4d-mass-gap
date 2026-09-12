import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterCore

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

/-- The assembled joint spectral/operator origin is the zero vector in the
augmented finite-parameter space. -/
@[simp]
theorem continuousLinearMapJointSpectralOperatorParameter_zero_zero
    (m : ℕ) :
    continuousLinearMapJointSpectralOperatorParameter m 0 0 = 0 := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp

end MathlibAnalytic
end MGAP4D
