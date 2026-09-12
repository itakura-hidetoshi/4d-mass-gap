import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicBinaryExactResponseGeometricControl
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData

/-- A common Lipschitz factor controls the selected plaquette expectation on
every fixed trajectory lattice. -/
structure UniformFixedLatticePlaquetteCouplingLipschitzBound
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) where
  factor : Real
  factor_nonneg : 0 <= factor
  abs_plaquetteExpectation_sub_le :
    forall (k : Nat) (beta0 beta1 : Real)
      (hBeta0 : 0 <= beta0) (hBeta1 : 0 <= beta1),
      abs (D.trajectory.plaquetteExpectationAtBeta k beta1 hBeta1 -
        D.trajectory.plaquetteExpectationAtBeta k beta0 hBeta0) <=
        factor * abs (beta1 - beta0)

namespace UniformFixedLatticePlaquetteCouplingLipschitzBound

variable {D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData}

/-- Uniform fixed-lattice coupling control supplies the exact coupling-response
certificate used by the weak-convergence bridge. -/
noncomputable def toExactCouplingResponseLipschitzBound
    (C : UniformFixedLatticePlaquetteCouplingLipschitzBound D) :
    ExactCouplingResponseLipschitzBound D :=
  { factor := C.factor
    factor_nonneg := C.factor_nonneg
    abs_couplingResponse_le := by
      intro n
      unfold couplingResponseIncrement
      exact C.abs_plaquetteExpectation_sub_le (n + 1)
        (D.trajectory.beta n) (D.trajectory.beta (n + 1))
        (D.trajectory.beta_nonneg n) (D.trajectory.beta_nonneg (n + 1)) }

end UniformFixedLatticePlaquetteCouplingLipschitzBound

end Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData

end

end MathlibAnalytic
end MGAP4D
