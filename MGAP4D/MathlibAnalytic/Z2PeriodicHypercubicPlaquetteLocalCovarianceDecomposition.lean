import MGAP4D.MathlibAnalytic.FiniteGibbsCovarianceFiniteSum
import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicPlaquetteExpectationBetaDerivative
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

namespace Z2PeriodicHypercubicPlaquetteTrajectory

noncomputable local instance fixedSystemConfigurationFintypeForLocalCovariance
    (T : Z2PeriodicHypercubicPlaquetteTrajectory) (k : Nat) :
    Fintype (T.fixedSystem k).Configuration :=
  Fintype.ofFinite (T.fixedSystem k).Configuration

/-- One plaquette-local term of the Wilson action on the canonical fixed
finite lattice. -/
noncomputable def fixedPlaquetteActionTerm
    (T : Z2PeriodicHypercubicPlaquetteTrajectory)
    (k : Nat) (p : (T.fixedSystem k).Plaquette) :
    (T.fixedSystem k).Configuration -> Real :=
  fun A => (T.fixedSystem k).plaquetteEnergy
    ((T.fixedSystem k).plaquetteHolonomy A p)

/-- The canonical fixed Wilson action is exactly the finite sum of its
plaquette-local terms. -/
theorem fixedWilsonAction_eq_sum_fixedPlaquetteActionTerm
    (T : Z2PeriodicHypercubicPlaquetteTrajectory) (k : Nat) :
    T.fixedWilsonAction k =
      fun A => Finset.univ.sum fun p : (T.fixedSystem k).Plaquette =>
        T.fixedPlaquetteActionTerm k p A := by
  funext A
  rfl

/-- Covariance of the selected plaquette observable with one plaquette-local
Wilson action term, under the full fixed-lattice Gibbs law. -/
noncomputable def fixedPlaquetteLocalCovariance
    (T : Z2PeriodicHypercubicPlaquetteTrajectory)
    (k : Nat) (p : (T.fixedSystem k).Plaquette)
    (beta : Real) : Real :=
  FiniteGibbsExpectationBetaDerivative.covarianceUnder
    (T.fixedPlaquetteObservable k)
    (T.fixedPlaquetteActionTerm k p)
    (T.fixedWilsonAction k) beta

/-- The plaquette-action covariance is the exact finite sum of the local
plaquette covariances. -/
theorem fixedPlaquetteActionCovariance_eq_sum_localCovariance
    (T : Z2PeriodicHypercubicPlaquetteTrajectory)
    (k : Nat) (beta : Real) :
    T.fixedPlaquetteActionCovariance k beta =
      Finset.univ.sum fun p : (T.fixedSystem k).Plaquette =>
        T.fixedPlaquetteLocalCovariance k p beta := by
  unfold fixedPlaquetteActionCovariance fixedPlaquetteLocalCovariance
  exact
    FiniteGibbsExpectationBetaDerivative.covariance_eq_finset_sum_covarianceUnder
      (Finset.univ : Finset (T.fixedSystem k).Plaquette)
      (T.fixedPlaquetteObservable k)
      (T.fixedWilsonAction k)
      (T.fixedPlaquetteActionTerm k)
      beta
      (T.fixedWilsonAction_eq_sum_fixedPlaquetteActionTerm k)

/-- Absolute plaquette-action covariance is bounded by the sum of absolute
local plaquette covariances. -/
theorem abs_fixedPlaquetteActionCovariance_le_sum_abs_localCovariance
    (T : Z2PeriodicHypercubicPlaquetteTrajectory)
    (k : Nat) (beta : Real) :
    abs (T.fixedPlaquetteActionCovariance k beta) <=
      Finset.univ.sum fun p : (T.fixedSystem k).Plaquette =>
        abs (T.fixedPlaquetteLocalCovariance k p beta) := by
  unfold fixedPlaquetteActionCovariance fixedPlaquetteLocalCovariance
  exact
    FiniteGibbsExpectationBetaDerivative.abs_covariance_le_sum_abs_covarianceUnder
      (Finset.univ : Finset (T.fixedSystem k).Plaquette)
      (T.fixedPlaquetteObservable k)
      (T.fixedWilsonAction k)
      (T.fixedPlaquetteActionTerm k)
      beta
      (T.fixedWilsonAction_eq_sum_fixedPlaquetteActionTerm k)

end Z2PeriodicHypercubicPlaquetteTrajectory

end

end MathlibAnalytic
end MGAP4D
