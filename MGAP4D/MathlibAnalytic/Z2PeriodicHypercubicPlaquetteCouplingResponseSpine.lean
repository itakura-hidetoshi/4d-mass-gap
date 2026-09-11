import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicAdjacentCovarianceCouplingBridge
import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicPlaquetteCovarianceCouplingBridge

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData

/-- Aggregate coupling-response constructor from a covariance bound on every
fixed lattice and every coupling. -/
noncomputable def exactCouplingResponseOfUniformCovariance
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (C : UniformFixedPlaquetteActionCovarianceBound D) :
    ExactCouplingResponseLipschitzBound D :=
  C.toExactCouplingResponseLipschitzBound

/-- Aggregate coupling-response constructor from covariance bounds only on the
adjacent coupling intervals used by the trajectory. -/
noncomputable def exactCouplingResponseOfAdjacentCovariance
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (C : AdjacentTrajectoryPlaquetteActionCovarianceBound D) :
    ExactCouplingResponseLipschitzBound D :=
  C.toExactCouplingResponseLipschitzBound

end Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData

end

end MathlibAnalytic
end MGAP4D
