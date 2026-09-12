import MGAP4D.MathlibAnalytic.FiniteExponentialShellGeometricBound
import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicGeometricLocalCovarianceMajorant
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set
open scoped BigOperators

noncomputable section

namespace Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData

/-- Exponential local covariance decay and exponential shell-cardinality growth
on every adjacent trajectory coupling interval. -/
structure AdjacentTrajectoryExponentialShellCovarianceControl
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) where
  covariancePrefactor : Real
  shellPrefactor : Real
  shellGrowth : Real
  ratio : Real
  covariancePrefactor_nonneg : 0 <= covariancePrefactor
  shellPrefactor_nonneg : 0 <= shellPrefactor
  shellGrowth_nonneg : 0 <= shellGrowth
  ratio_nonneg : 0 <= ratio
  ratio_lt_one : ratio < 1
  growth_mul_ratio_lt_one : shellGrowth * ratio < 1
  distance :
    (n : Nat) ->
      (D.trajectory.fixedSystem (n + 1)).Plaquette -> Nat
  radius : Nat -> Nat
  distance_lt_radius :
    forall (n : Nat)
      (p : (D.trajectory.fixedSystem (n + 1)).Plaquette),
      distance n p < radius n
  shell_card_real_le :
    forall (n m : Nat),
      ((Finset.univ.filter fun
        p : (D.trajectory.fixedSystem (n + 1)).Plaquette =>
          distance n p = m).card : Real) <=
        shellPrefactor * shellGrowth ^ m
  abs_local_covariance_le :
    forall (n : Nat) (beta : Real),
      beta ∈ Set.uIcc (D.trajectory.beta n) (D.trajectory.beta (n + 1)) ->
      forall p : (D.trajectory.fixedSystem (n + 1)).Plaquette,
        abs (D.trajectory.fixedPlaquetteLocalCovariance
          (n + 1) p beta) <=
          covariancePrefactor * ratio ^ distance n p

namespace AdjacentTrajectoryExponentialShellCovarianceControl

variable {D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData}

/-- Exponential shell growth and faster covariance decay produce the geometric
local covariance control with explicit shell mass. -/
noncomputable def toAdjacentTrajectoryGeometricLocalPlaquetteCovarianceControl
    (C : AdjacentTrajectoryExponentialShellCovarianceControl D) :
    AdjacentTrajectoryGeometricLocalPlaquetteCovarianceControl D :=
  { prefactor := C.covariancePrefactor
    shellMass := C.shellPrefactor / (1 - C.shellGrowth * C.ratio)
    ratio := C.ratio
    prefactor_nonneg := C.covariancePrefactor_nonneg
    shellMass_nonneg := by
      exact div_nonneg C.shellPrefactor_nonneg
        (sub_nonneg.mpr (le_of_lt C.growth_mul_ratio_lt_one))
    ratio_nonneg := C.ratio_nonneg
    ratio_lt_one := C.ratio_lt_one
    distance := C.distance
    abs_local_covariance_le := C.abs_local_covariance_le
    sum_geometric_weights_le := by
      intro n
      let S :
          FiniteDistanceShellGeometricSum.FiniteExponentialShellControl
            (D.trajectory.fixedSystem (n + 1)).Plaquette :=
        { distance := C.distance n
          radius := C.radius n
          ratio := C.ratio
          shellPrefactor := C.shellPrefactor
          shellGrowth := C.shellGrowth
          ratio_nonneg := C.ratio_nonneg
          ratio_lt_one := C.ratio_lt_one
          shellPrefactor_nonneg := C.shellPrefactor_nonneg
          shellGrowth_nonneg := C.shellGrowth_nonneg
          growth_mul_ratio_lt_one := C.growth_mul_ratio_lt_one
          distance_lt_radius := C.distance_lt_radius n
          shell_card_real_le := C.shell_card_real_le n }
      exact S.sum_pow_distance_le_explicit }

/-- The resulting exact coupling-response factor is explicitly
`covariancePrefactor * shellPrefactor / (1 - shellGrowth * ratio)`. -/
noncomputable def toExactCouplingResponseLipschitzBound
    (C : AdjacentTrajectoryExponentialShellCovarianceControl D) :
    ExactCouplingResponseLipschitzBound D :=
  C.toAdjacentTrajectoryGeometricLocalPlaquetteCovarianceControl
    |>.toExactCouplingResponseLipschitzBound

/-- The exact response certificate carries the explicit product of the local
covariance prefactor and the summable shell mass. -/
theorem toExactCouplingResponseLipschitzBound_factor
    (C : AdjacentTrajectoryExponentialShellCovarianceControl D) :
    C.toExactCouplingResponseLipschitzBound.factor =
      C.covariancePrefactor *
        (C.shellPrefactor / (1 - C.shellGrowth * C.ratio)) :=
  rfl

end AdjacentTrajectoryExponentialShellCovarianceControl

end Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData

end

end MathlibAnalytic
end MGAP4D
