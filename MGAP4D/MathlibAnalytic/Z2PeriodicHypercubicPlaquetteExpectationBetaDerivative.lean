import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicPlaquetteFixedGibbsExpectation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace Z2PeriodicHypercubicPlaquetteTrajectory

noncomputable local instance fixedSystemConfigurationFintypeForDerivative
    (T : Z2PeriodicHypercubicPlaquetteTrajectory) (k : Nat) :
    Fintype (T.fixedSystem k).Configuration :=
  Fintype.ofFinite (T.fixedSystem k).Configuration

noncomputable def fixedPlaquetteActionCovariance
    (T : Z2PeriodicHypercubicPlaquetteTrajectory)
    (k : Nat) (beta : Real) : Real :=
  FiniteGibbsExpectationBetaDerivative.covariance
    (T.fixedPlaquetteObservable k) (T.fixedWilsonAction k) beta

theorem hasDerivAt_fixedPlaquetteGibbsExpectation_eq_neg_covariance
    (T : Z2PeriodicHypercubicPlaquetteTrajectory)
    (k : Nat) (beta : Real) :
    HasDerivAt
      (T.fixedPlaquetteGibbsExpectation k)
      (-T.fixedPlaquetteActionCovariance k beta) beta := by
  simpa [fixedPlaquetteGibbsExpectation, fixedPlaquetteActionCovariance] using
    (FiniteGibbsExpectationBetaDerivative.hasDerivAt_expectation_eq_neg_covariance
      (T.fixedPlaquetteObservable k) (T.fixedWilsonAction k) beta)

theorem deriv_fixedPlaquetteGibbsExpectation_eq_neg_covariance
    (T : Z2PeriodicHypercubicPlaquetteTrajectory)
    (k : Nat) (beta : Real) :
    deriv (T.fixedPlaquetteGibbsExpectation k) beta =
      -T.fixedPlaquetteActionCovariance k beta :=
  (T.hasDerivAt_fixedPlaquetteGibbsExpectation_eq_neg_covariance k beta).deriv

end Z2PeriodicHypercubicPlaquetteTrajectory

end

end MathlibAnalytic
end MGAP4D
