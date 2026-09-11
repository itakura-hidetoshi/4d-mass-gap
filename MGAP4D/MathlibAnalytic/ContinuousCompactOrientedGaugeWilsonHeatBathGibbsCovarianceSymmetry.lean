import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonFiniteHeatBathGibbsCovariance
import Mathlib.Tactic

/-!
# One-link Gibbs covariance symmetry for the compact Wilson heat bath

The current compact orientation-correct Wilson carrier already provides:

* exact Gibbs stationarity for every finite ordered heat-bath kernel;
* the one-link conditional expectation as a bounded-continuous Feller operator;
* exact self-adjointness of the one-link heat-bath projection for the Gibbs pairing.

This file packages those facts at the covariance level.  For the one-link
conditional expectation `P_e`, we prove

`Cov(P_e F, O) = Cov(F, P_e O)`.

This is the algebraic entry point for later fluctuation decompositions
`Q_e = I - P_e` and support-localized Dobrushin covariance estimates.  No
covariance decay, continuum clustering, positive physical mass, OS Hamiltonian
gap, or uniform factorial-continuum Dobrushin threshold is asserted here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

private theorem continuous_compact_oriented_bcf_abs_le_norm_covariance_symmetry
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration) :
    |O A| ≤ ‖O‖ := by
  simpa [Real.norm_eq_abs] using O.norm_coe_le_norm A

private theorem
    continuous_compact_oriented_singleLinkConditionalExpectationContinuousBCF_coe_eq_projection_covariance_symmetry
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    (fun A : C.base.Configuration =>
      C.singleLinkConditionalExpectationContinuousBCF target O A) =
      C.singleLinkHeatBathProjection target (fun A => O A) := by
  funext A
  rw [continuous_compact_oriented_singleLinkConditionalExpectationContinuousBCF_apply]
  rfl

/-- The one-link bounded-continuous conditional expectation preserves the
canonical finite-volume Wilson Gibbs mean. -/
theorem continuous_compact_oriented_gibbsMeanReal_singleLinkConditionalExpectationContinuousBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.gibbsMeanReal
        (fun A => C.singleLinkConditionalExpectationContinuousBCF target O A) =
      C.gibbsMeanReal (fun A => O A) := by
  have hMean :=
    continuous_compact_oriented_gibbsMeanReal_finiteSingleLinkHeatBathExpectationBCF
      C [target] O
  have hEq :
      (fun A : C.base.Configuration =>
        C.finiteSingleLinkHeatBathExpectationBCF [target] O A) =
      (fun A : C.base.Configuration =>
        C.singleLinkConditionalExpectationContinuousBCF target O A) := by
    funext A
    rw [← continuous_compact_oriented_finiteSingleLinkHeatBathContinuousBCF_eq_expectationBCF
      C [target] O A]
    simp
  rw [hEq] at hMean
  exact hMean

/-- A single exact heat-bath conditional expectation is self-adjoint for the
finite-volume Wilson Gibbs covariance. -/
theorem continuous_compact_oriented_singleLinkConditionalExpectationContinuousBCF_gibbsCovariance_symm
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (F O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.gibbsCovarianceReal
        (fun A => C.singleLinkConditionalExpectationContinuousBCF target F A)
        (fun A => O A) =
      C.gibbsCovarianceReal
        (fun A => F A)
        (fun A => C.singleLinkConditionalExpectationContinuousBCF target O A) := by
  have hPair :=
    continuous_compact_oriented_singleLinkHeatBathProjection_gibbsPairing_symm
      C target (fun A => F A) (fun A => O A)
      F.continuous.stronglyMeasurable O.continuous.stronglyMeasurable
      ‖F‖ ‖O‖ (norm_nonneg _) (norm_nonneg _)
      (fun A => continuous_compact_oriented_bcf_abs_le_norm_covariance_symmetry F A)
      (fun A => continuous_compact_oriented_bcf_abs_le_norm_covariance_symmetry O A)
  have hFProjection :=
    continuous_compact_oriented_singleLinkConditionalExpectationContinuousBCF_coe_eq_projection_covariance_symmetry
      C target F
  have hOProjection :=
    continuous_compact_oriented_singleLinkConditionalExpectationContinuousBCF_coe_eq_projection_covariance_symmetry
      C target O
  rw [← hFProjection, ← hOProjection] at hPair
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsCovarianceReal
  rw [hPair,
    continuous_compact_oriented_gibbsMeanReal_singleLinkConditionalExpectationContinuousBCF
      C target F,
    continuous_compact_oriented_gibbsMeanReal_singleLinkConditionalExpectationContinuousBCF
      C target O]

end

end MathlibAnalytic
end MGAP4D
