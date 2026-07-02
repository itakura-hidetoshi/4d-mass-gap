import MGAP4D.MathlibAnalytic.FiniteOrientedWilsonGibbsExpectationFiniteSum
import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicBinaryExactGeometryBetaSplitting
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace Z2PeriodicHypercubicPlaquetteTrajectory

/-- The fixed-lattice plaquette expectation at a nonnegative coupling is exactly
the normalized finite-sum Gibbs expectation. -/
theorem plaquetteExpectationAtBeta_eq_finiteGibbsExpectation
    (T : Z2PeriodicHypercubicPlaquetteTrajectory)
    (k : Nat) (beta : Real) (hBeta : 0 <= beta) :
    T.plaquetteExpectationAtBeta k beta hBeta =
      FiniteGibbsExpectationBetaDerivative.expectation
        (T.plaquetteObservableAtBeta k beta hBeta)
        (T.systemAtBeta k beta hBeta).wilsonAction beta := by
  simpa [plaquetteExpectationAtBeta] using
    (finite_oriented_gibbsIntegral_eq_finiteGibbsExpectation
      (T.systemAtBeta k beta hBeta)
      (T.plaquetteObservableAtBeta k beta hBeta))

end Z2PeriodicHypercubicPlaquetteTrajectory

end

end MathlibAnalytic
end MGAP4D
