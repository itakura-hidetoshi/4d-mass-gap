import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicAdjacentCovarianceCouplingBridge
import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicPlaquetteLocalCovarianceDecomposition
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set
open scoped BigOperators

noncomputable section

namespace Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData

/-- A common bound for the sum of absolute local plaquette covariances on each
adjacent coupling interval used by the trajectory. -/
structure AdjacentTrajectoryLocalPlaquetteCovarianceSumBound
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) where
  factor : Real
  factor_nonneg : 0 <= factor
  sum_abs_local_covariance_le :
    forall (n : Nat) (beta : Real),
      beta ∈ Set.uIcc (D.trajectory.beta n) (D.trajectory.beta (n + 1)) ->
      Finset.univ.sum
        (fun p : (D.trajectory.fixedSystem (n + 1)).Plaquette =>
          abs (D.trajectory.fixedPlaquetteLocalCovariance (n + 1) p beta)) <=
        factor

namespace AdjacentTrajectoryLocalPlaquetteCovarianceSumBound

variable {D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData}

/-- Local plaquette covariance summability yields the adjacent-interval bound
for covariance with the full Wilson action. -/
noncomputable def toAdjacentTrajectoryPlaquetteActionCovarianceBound
    (C : AdjacentTrajectoryLocalPlaquetteCovarianceSumBound D) :
    AdjacentTrajectoryPlaquetteActionCovarianceBound D :=
  { factor := C.factor
    factor_nonneg := C.factor_nonneg
    abs_covariance_le := by
      intro n beta hBeta
      exact
        (D.trajectory.abs_fixedPlaquetteActionCovariance_le_sum_abs_localCovariance
          (n + 1) beta).trans
          (C.sum_abs_local_covariance_le n beta hBeta) }

/-- Local plaquette covariance summability directly supplies the exact
coupling-response certificate used by the full weak-convergence bridge. -/
noncomputable def toExactCouplingResponseLipschitzBound
    (C : AdjacentTrajectoryLocalPlaquetteCovarianceSumBound D) :
    ExactCouplingResponseLipschitzBound D :=
  C.toAdjacentTrajectoryPlaquetteActionCovarianceBound
    |>.toExactCouplingResponseLipschitzBound

end AdjacentTrajectoryLocalPlaquetteCovarianceSumBound

end Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData

end

end MathlibAnalytic
end MGAP4D
