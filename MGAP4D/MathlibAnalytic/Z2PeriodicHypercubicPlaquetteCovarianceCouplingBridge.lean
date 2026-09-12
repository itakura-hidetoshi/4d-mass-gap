import MGAP4D.MathlibAnalytic.FiniteGibbsExpectationCovarianceLipschitz
import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicPlaquetteCouplingLipschitzBridge
import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicPlaquetteExpectationBetaDerivative
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData

/-- A common bound for the covariance of the selected plaquette observable with
the full Wilson action on every fixed trajectory lattice and at every coupling. -/
structure UniformFixedPlaquetteActionCovarianceBound
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) where
  factor : Real
  factor_nonneg : 0 <= factor
  abs_covariance_le :
    forall (k : Nat) (beta : Real),
      abs (D.trajectory.fixedPlaquetteActionCovariance k beta) <= factor

namespace UniformFixedPlaquetteActionCovarianceBound

variable {D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData}

noncomputable local instance fixedSystemConfigurationFintypeForCovarianceBridge
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) (k : Nat) :
    Fintype (D.trajectory.fixedSystem k).Configuration :=
  Fintype.ofFinite (D.trajectory.fixedSystem k).Configuration

/-- A lattice-uniform covariance estimate yields a common fixed-lattice
Lipschitz factor for the selected plaquette expectation. -/
noncomputable def toUniformFixedLatticePlaquetteCouplingLipschitzBound
    (C : UniformFixedPlaquetteActionCovarianceBound D) :
    UniformFixedLatticePlaquetteCouplingLipschitzBound D :=
  { factor := C.factor
    factor_nonneg := C.factor_nonneg
    abs_plaquetteExpectation_sub_le := by
      intro k beta0 beta1 hBeta0 hBeta1
      rw [D.trajectory.plaquetteExpectationAtBeta_eq_fixedPlaquetteGibbsExpectation
          k beta1 hBeta1,
        D.trajectory.plaquetteExpectationAtBeta_eq_fixedPlaquetteGibbsExpectation
          k beta0 hBeta0]
      let Ck : FiniteGibbsExpectationBetaDerivative.UniformCovarianceBound
          (D.trajectory.fixedPlaquetteObservable k)
          (D.trajectory.fixedWilsonAction k) :=
        { factor := C.factor
          factor_nonneg := C.factor_nonneg
          abs_covariance_le := by
            intro beta
            simpa [Z2PeriodicHypercubicPlaquetteTrajectory.fixedPlaquetteActionCovariance]
              using C.abs_covariance_le k beta }
      simpa [Z2PeriodicHypercubicPlaquetteTrajectory.fixedPlaquetteGibbsExpectation] using
        Ck.abs_expectation_sub_le beta0 beta1 }

/-- A lattice-uniform plaquette-action covariance estimate directly supplies
the exact coupling-response certificate used by the weak-convergence bridge. -/
noncomputable def toExactCouplingResponseLipschitzBound
    (C : UniformFixedPlaquetteActionCovarianceBound D) :
    ExactCouplingResponseLipschitzBound D :=
  C.toUniformFixedLatticePlaquetteCouplingLipschitzBound
    |>.toExactCouplingResponseLipschitzBound

end UniformFixedPlaquetteActionCovarianceBound

end Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData

end

end MathlibAnalytic
end MGAP4D
