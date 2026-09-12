import MGAP4D.MathlibAnalytic.PeriodicHypercubicPlaquetteDistanceShellBound
import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicExponentialShellCovarianceControl
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set

noncomputable section

namespace Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData

/-- Exponential decay of local plaquette covariances measured using the concrete
shared-link graph distance on each periodic trajectory lattice. The geometric
shell data are no longer assumptions: they are supplied by the explicit
periodic hypercubic distance-shell bound with growth base `24`. -/
structure AdjacentTrajectoryConcretePlaquetteDistanceCovarianceDecay
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) where
  covariancePrefactor : Real
  ratio : Real
  covariancePrefactor_nonneg : 0 ≤ covariancePrefactor
  ratio_nonneg : 0 ≤ ratio
  twentyFour_mul_ratio_lt_one : (24 : Real) * ratio < 1
  abs_local_covariance_le :
    ∀ (n : Nat) (beta : Real),
      beta ∈ Set.uIcc (D.trajectory.beta n) (D.trajectory.beta (n + 1)) →
      ∀ p : (D.trajectory.fixedSystem (n + 1)).Plaquette,
        abs (D.trajectory.fixedPlaquetteLocalCovariance
          (n + 1) p beta) ≤
          covariancePrefactor * ratio ^
            periodicHypercubicPlaquetteDistance
              (D.trajectory.sideLength (n + 1))
              (D.trajectory.plaquette (n + 1)) p

namespace AdjacentTrajectoryConcretePlaquetteDistanceCovarianceDecay

variable {D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData}

/-- The concrete periodic geometry packages the local decay hypothesis into the
abstract exponential-shell covariance certificate with shell prefactor `1` and
shell growth `24`. -/
noncomputable def toAdjacentTrajectoryExponentialShellCovarianceControl
    (C : AdjacentTrajectoryConcretePlaquetteDistanceCovarianceDecay D) :
    AdjacentTrajectoryExponentialShellCovarianceControl D :=
  { covariancePrefactor := C.covariancePrefactor
    shellPrefactor := 1
    shellGrowth := 24
    ratio := C.ratio
    covariancePrefactor_nonneg := C.covariancePrefactor_nonneg
    shellPrefactor_nonneg := by norm_num
    shellGrowth_nonneg := by norm_num
    ratio_nonneg := C.ratio_nonneg
    ratio_lt_one := by
      nlinarith [C.ratio_nonneg, C.twentyFour_mul_ratio_lt_one]
    growth_mul_ratio_lt_one := C.twentyFour_mul_ratio_lt_one
    distance := fun n p =>
      periodicHypercubicPlaquetteDistance
        (D.trajectory.sideLength (n + 1))
        (D.trajectory.plaquette (n + 1)) p
    radius := fun n =>
      periodicHypercubicPlaquetteDistanceRadius
        (D.trajectory.sideLength (n + 1))
    distance_lt_radius := by
      intro n p
      exact periodicHypercubicPlaquetteDistance_lt_radius
        (D.trajectory.sideLength (n + 1))
        (D.trajectory.sideLength_ge_two (n + 1))
        (D.trajectory.plaquette (n + 1)) p
    shell_card_real_le := by
      intro n m
      have hPos : 0 < D.trajectory.sideLength (n + 1) :=
        lt_of_lt_of_le (by norm_num)
          (D.trajectory.sideLength_ge_two (n + 1))
      letI : NeZero (D.trajectory.sideLength (n + 1)) :=
        ⟨Nat.ne_of_gt hPos⟩
      simpa [periodicHypercubicPlaquetteDistanceShell] using
        (periodicHypercubicPlaquetteDistanceShell_card_real_le
          (D.trajectory.sideLength (n + 1))
          (D.trajectory.sideLength_ge_two (n + 1))
          (D.trajectory.plaquette (n + 1)) m)
    abs_local_covariance_le := C.abs_local_covariance_le }

/-- Concrete local covariance decay therefore yields the exact fixed-lattice
coupling-response Lipschitz certificate. -/
noncomputable def toExactCouplingResponseLipschitzBound
    (C : AdjacentTrajectoryConcretePlaquetteDistanceCovarianceDecay D) :
    ExactCouplingResponseLipschitzBound D :=
  C.toAdjacentTrajectoryExponentialShellCovarianceControl
    |>.toExactCouplingResponseLipschitzBound

/-- The resulting exact coupling-response factor is the concrete expression
`A / (1 - 24 r)`, written in the multiplication form inherited from the
certificate chain. -/
theorem toExactCouplingResponseLipschitzBound_factor
    (C : AdjacentTrajectoryConcretePlaquetteDistanceCovarianceDecay D) :
    C.toExactCouplingResponseLipschitzBound.factor =
      C.covariancePrefactor * (1 / (1 - 24 * C.ratio)) :=
  rfl

end AdjacentTrajectoryConcretePlaquetteDistanceCovarianceDecay

end Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData

end

end MathlibAnalytic
end MGAP4D
