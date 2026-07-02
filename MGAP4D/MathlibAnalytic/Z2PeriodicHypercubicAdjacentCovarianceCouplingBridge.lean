import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicBinaryExactResponseGeometricControl
import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicPlaquetteExpectationBetaDerivative
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set

noncomputable section

namespace Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData

/-- A common covariance bound only on the adjacent coupling intervals actually
used by the trajectory coupling-response increments. -/
structure AdjacentTrajectoryPlaquetteActionCovarianceBound
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) where
  factor : Real
  factor_nonneg : 0 <= factor
  abs_covariance_le :
    forall (n : Nat) (beta : Real),
      beta ∈ Set.uIcc (D.trajectory.beta n) (D.trajectory.beta (n + 1)) ->
      abs (D.trajectory.fixedPlaquetteActionCovariance (n + 1) beta) <= factor

namespace AdjacentTrajectoryPlaquetteActionCovarianceBound

variable {D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData}

/-- Covariance control on each adjacent trajectory interval is sufficient for
the exact coupling-response certificate; no global all-coupling bound is needed. -/
noncomputable def toExactCouplingResponseLipschitzBound
    (C : AdjacentTrajectoryPlaquetteActionCovarianceBound D) :
    ExactCouplingResponseLipschitzBound D :=
  { factor := C.factor
    factor_nonneg := C.factor_nonneg
    abs_couplingResponse_le := by
      intro n
      unfold couplingResponseIncrement
      rw [D.trajectory.plaquetteExpectationAtBeta_eq_fixedPlaquetteGibbsExpectation
          (n + 1) (D.trajectory.beta (n + 1))
          (D.trajectory.beta_nonneg (n + 1)),
        D.trajectory.plaquetteExpectationAtBeta_eq_fixedPlaquetteGibbsExpectation
          (n + 1) (D.trajectory.beta n)
          (D.trajectory.beta_nonneg n)]
      have hDifferentiable :
          forall beta : Real,
            beta ∈ Set.uIcc (D.trajectory.beta n) (D.trajectory.beta (n + 1)) ->
            DifferentiableAt Real
              (D.trajectory.fixedPlaquetteGibbsExpectation (n + 1)) beta := by
        intro beta _hBeta
        exact
          (D.trajectory.hasDerivAt_fixedPlaquetteGibbsExpectation_eq_neg_covariance
            (n + 1) beta).differentiableAt
      have hDerivativeBound :
          forall beta : Real,
            beta ∈ Set.uIcc (D.trajectory.beta n) (D.trajectory.beta (n + 1)) ->
            norm (deriv
              (D.trajectory.fixedPlaquetteGibbsExpectation (n + 1)) beta) <=
              C.factor := by
        intro beta hBeta
        rw [D.trajectory.deriv_fixedPlaquetteGibbsExpectation_eq_neg_covariance]
        simpa [Real.norm_eq_abs] using C.abs_covariance_le n beta hBeta
      have hConvex :
          Convex Real
            (Set.uIcc (D.trajectory.beta n) (D.trajectory.beta (n + 1))) := by
        unfold Set.uIcc
        exact convex_Icc _ _
      have hLeft :
          D.trajectory.beta n ∈
            Set.uIcc (D.trajectory.beta n) (D.trajectory.beta (n + 1)) := by
        unfold Set.uIcc
        exact ⟨min_le_left _ _, le_max_left _ _⟩
      have hRight :
          D.trajectory.beta (n + 1) ∈
            Set.uIcc (D.trajectory.beta n) (D.trajectory.beta (n + 1)) := by
        unfold Set.uIcc
        exact ⟨min_le_right _ _, le_max_right _ _⟩
      have h := hConvex.norm_image_sub_le_of_norm_deriv_le
        hDifferentiable hDerivativeBound hLeft hRight
      simpa [Real.norm_eq_abs] using h }

end AdjacentTrajectoryPlaquetteActionCovarianceBound

end Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData

end

end MathlibAnalytic
end MGAP4D
