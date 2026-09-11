import MGAP4D.MathlibAnalytic.FiniteDistanceShellGeometricSum
import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicGeometricLocalCovarianceMajorant
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set
open scoped BigOperators

noncomputable section

namespace Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData

/-- Trajectory-dependent distance-shell data combining exponential local
covariance decay with uniform shell-cardinality summability. -/
structure AdjacentTrajectoryDistanceShellCovarianceControl
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
  radius : Nat -> Nat
  shellCardBound : Nat -> Nat -> Nat
  distance_lt_radius :
    forall (n : Nat)
      (p : (D.trajectory.fixedSystem (n + 1)).Plaquette),
      distance n p < radius n
  shell_card_le :
    forall (n m : Nat),
      (Finset.univ.filter fun
        p : (D.trajectory.fixedSystem (n + 1)).Plaquette =>
          distance n p = m).card <= shellCardBound n m
  weighted_shell_sum_le :
    forall n : Nat,
      Finset.sum (Finset.range (radius n)) (fun m =>
        (shellCardBound n m : Real) * ratio ^ m) <= shellMass
  abs_local_covariance_le :
    forall (n : Nat) (beta : Real),
      beta ∈ Set.uIcc (D.trajectory.beta n) (D.trajectory.beta (n + 1)) ->
      forall p : (D.trajectory.fixedSystem (n + 1)).Plaquette,
        abs (D.trajectory.fixedPlaquetteLocalCovariance
          (n + 1) p beta) <=
          prefactor * ratio ^ distance n p

namespace AdjacentTrajectoryDistanceShellCovarianceControl

variable {D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData}

/-- Distance-shell cardinality control supplies the uniform geometric-weight
bound required by the local covariance majorant. -/
noncomputable def toAdjacentTrajectoryGeometricLocalPlaquetteCovarianceControl
    (C : AdjacentTrajectoryDistanceShellCovarianceControl D) :
    AdjacentTrajectoryGeometricLocalPlaquetteCovarianceControl D :=
  { prefactor := C.prefactor
    shellMass := C.shellMass
    ratio := C.ratio
    prefactor_nonneg := C.prefactor_nonneg
    shellMass_nonneg := C.shellMass_nonneg
    ratio_nonneg := C.ratio_nonneg
    ratio_lt_one := C.ratio_lt_one
    distance := C.distance
    abs_local_covariance_le := C.abs_local_covariance_le
    sum_geometric_weights_le := by
      intro n
      let S :
          FiniteDistanceShellGeometricSum.FiniteGeometricShellControl
            (D.trajectory.fixedSystem (n + 1)).Plaquette :=
        { distance := C.distance n
          radius := C.radius n
          shellCardBound := C.shellCardBound n
          shellMass := C.shellMass
          ratio := C.ratio
          shellMass_nonneg := C.shellMass_nonneg
          ratio_nonneg := C.ratio_nonneg
          ratio_lt_one := C.ratio_lt_one
          distance_lt_radius := C.distance_lt_radius n
          shell_card_le := C.shell_card_le n
          weighted_shell_sum_le := C.weighted_shell_sum_le n }
      exact S.sum_pow_distance_le }

/-- Exponential local covariance decay plus uniformly summable distance shells
directly yields the exact coupling-response certificate. -/
noncomputable def toExactCouplingResponseLipschitzBound
    (C : AdjacentTrajectoryDistanceShellCovarianceControl D) :
    ExactCouplingResponseLipschitzBound D :=
  C.toAdjacentTrajectoryGeometricLocalPlaquetteCovarianceControl
    |>.toExactCouplingResponseLipschitzBound

end AdjacentTrajectoryDistanceShellCovarianceControl

end Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData

end

end MathlibAnalytic
end MGAP4D
