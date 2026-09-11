import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicLocalCovarianceMajorantBridge
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set
open scoped BigOperators

noncomputable section

namespace Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData

/-- Exponential pointwise decay of local plaquette covariances, together with a
uniform bound on the total geometric weight over the finite periodic lattice. -/
structure AdjacentTrajectoryGeometricLocalPlaquetteCovarianceControl
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) where
  prefactor : Real
  shellMass : Real
  ratio : Real
  prefactor_nonneg : 0 <= prefactor
  shellMass_nonneg : 0 <= shellMass
  ratio_nonneg : 0 <= ratio
  ratio_lt_one : ratio < 1
  distance :
    (n : Nat) ->
      (D.trajectory.fixedSystem (n + 1)).Plaquette -> Nat
  abs_local_covariance_le :
    forall (n : Nat) (beta : Real),
      beta ∈ Set.uIcc (D.trajectory.beta n) (D.trajectory.beta (n + 1)) ->
      forall p : (D.trajectory.fixedSystem (n + 1)).Plaquette,
        abs (D.trajectory.fixedPlaquetteLocalCovariance
          (n + 1) p beta) <=
          prefactor * ratio ^ distance n p
  sum_geometric_weights_le :
    forall n : Nat,
      Finset.univ.sum
        (fun p : (D.trajectory.fixedSystem (n + 1)).Plaquette =>
          ratio ^ distance n p) <= shellMass

namespace AdjacentTrajectoryGeometricLocalPlaquetteCovarianceControl

variable {D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData}

/-- Exponential local covariance decay and a uniform geometric-weight bound
produce a uniformly summable plaquette-wise majorant. -/
noncomputable def toAdjacentTrajectoryLocalPlaquetteCovarianceMajorant
    (C : AdjacentTrajectoryGeometricLocalPlaquetteCovarianceControl D) :
    AdjacentTrajectoryLocalPlaquetteCovarianceMajorant D :=
  { factor := C.prefactor * C.shellMass
    factor_nonneg := mul_nonneg C.prefactor_nonneg C.shellMass_nonneg
    majorant := fun n p => C.prefactor * C.ratio ^ C.distance n p
    majorant_nonneg := by
      intro n p
      exact mul_nonneg C.prefactor_nonneg
        (pow_nonneg C.ratio_nonneg _)
    abs_local_covariance_le := C.abs_local_covariance_le
    sum_majorant_le := by
      intro n
      calc
        Finset.univ.sum
            (fun p : (D.trajectory.fixedSystem (n + 1)).Plaquette =>
              C.prefactor * C.ratio ^ C.distance n p) =
          C.prefactor *
            Finset.univ.sum
              (fun p : (D.trajectory.fixedSystem (n + 1)).Plaquette =>
                C.ratio ^ C.distance n p) := by
            rw [Finset.mul_sum]
        _ <= C.prefactor * C.shellMass :=
          mul_le_mul_of_nonneg_left
            (C.sum_geometric_weights_le n) C.prefactor_nonneg }

/-- Exponential local covariance decay with uniformly summable geometric
weights directly yields the exact coupling-response certificate. -/
noncomputable def toExactCouplingResponseLipschitzBound
    (C : AdjacentTrajectoryGeometricLocalPlaquetteCovarianceControl D) :
    ExactCouplingResponseLipschitzBound D :=
  C.toAdjacentTrajectoryLocalPlaquetteCovarianceMajorant
    |>.toExactCouplingResponseLipschitzBound

end AdjacentTrajectoryGeometricLocalPlaquetteCovarianceControl

end Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData

end

end MathlibAnalytic
end MGAP4D
