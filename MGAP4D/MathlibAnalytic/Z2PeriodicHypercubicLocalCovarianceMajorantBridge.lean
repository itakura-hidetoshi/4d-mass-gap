import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicLocalCovarianceCouplingBridge
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set
open scoped BigOperators

noncomputable section

namespace Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData

/-- A nonnegative plaquette-wise majorant for local covariances on each adjacent
trajectory coupling interval, together with a uniform bound on its finite sum. -/
structure AdjacentTrajectoryLocalPlaquetteCovarianceMajorant
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) where
  factor : Real
  factor_nonneg : 0 <= factor
  majorant :
    (n : Nat) ->
      (D.trajectory.fixedSystem (n + 1)).Plaquette -> Real
  majorant_nonneg :
    forall (n : Nat)
      (p : (D.trajectory.fixedSystem (n + 1)).Plaquette),
      0 <= majorant n p
  abs_local_covariance_le :
    forall (n : Nat) (beta : Real),
      beta ∈ Set.uIcc (D.trajectory.beta n) (D.trajectory.beta (n + 1)) ->
      forall p : (D.trajectory.fixedSystem (n + 1)).Plaquette,
        abs (D.trajectory.fixedPlaquetteLocalCovariance
          (n + 1) p beta) <= majorant n p
  sum_majorant_le :
    forall n : Nat,
      Finset.univ.sum
        (fun p : (D.trajectory.fixedSystem (n + 1)).Plaquette =>
          majorant n p) <= factor

namespace AdjacentTrajectoryLocalPlaquetteCovarianceMajorant

variable {D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData}

/-- A plaquette-wise majorant with uniformly bounded total mass yields the
adjacent-interval local covariance-sum certificate. -/
noncomputable def toAdjacentTrajectoryLocalPlaquetteCovarianceSumBound
    (C : AdjacentTrajectoryLocalPlaquetteCovarianceMajorant D) :
    AdjacentTrajectoryLocalPlaquetteCovarianceSumBound D :=
  { factor := C.factor
    factor_nonneg := C.factor_nonneg
    sum_abs_local_covariance_le := by
      intro n beta hBeta
      calc
        Finset.univ.sum
            (fun p : (D.trajectory.fixedSystem (n + 1)).Plaquette =>
              abs (D.trajectory.fixedPlaquetteLocalCovariance
                (n + 1) p beta)) <=
          Finset.univ.sum
            (fun p : (D.trajectory.fixedSystem (n + 1)).Plaquette =>
              C.majorant n p) := by
            apply Finset.sum_le_sum
            intro p _hp
            exact C.abs_local_covariance_le n beta hBeta p
        _ <= C.factor := C.sum_majorant_le n }

/-- A uniformly summable plaquette-wise covariance majorant directly supplies
the exact coupling-response certificate. -/
noncomputable def toExactCouplingResponseLipschitzBound
    (C : AdjacentTrajectoryLocalPlaquetteCovarianceMajorant D) :
    ExactCouplingResponseLipschitzBound D :=
  C.toAdjacentTrajectoryLocalPlaquetteCovarianceSumBound
    |>.toExactCouplingResponseLipschitzBound

end AdjacentTrajectoryLocalPlaquetteCovarianceMajorant

end Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData

end

end MathlibAnalytic
end MGAP4D
