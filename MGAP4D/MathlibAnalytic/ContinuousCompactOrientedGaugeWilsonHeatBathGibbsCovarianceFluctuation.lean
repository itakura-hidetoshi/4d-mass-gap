import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathGibbsCovarianceSymmetry
import Mathlib.Tactic

/-!
# One-link Gibbs covariance fluctuation carrier

For the exact compact Wilson one-link conditional expectation `P_e`, define the
bounded-continuous fluctuation operator

`Q_e O = O - P_e O`.

The preceding current-root carrier proves covariance self-adjointness of `P_e`.
This file adds the small bounded-continuous covariance algebra needed to pass
that symmetry to `Q_e` and proves

`Cov(Q_e F, O) = Cov(F, Q_e O)`.

The fluctuation also has exactly zero Gibbs mean.  These identities are the
local algebraic input for later support-localized Dobrushin covariance bounds.
No covariance decay, continuum clustering, positive physical mass, OS
Hamiltonian gap, or uniform factorial-continuum Dobrushin threshold is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

private theorem continuous_compact_oriented_bcf_integrable_gibbs_covariance_fluctuation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    Integrable (fun A => O A) C.gibbsMeasure := by
  apply continuous_compact_oriented_integrable_of_uniform_bound
    C.gibbsMeasure (fun A => O A) O.continuous.stronglyMeasurable ‖O‖
  intro A
  simpa [Real.norm_eq_abs] using O.norm_coe_le_norm A

/-- The finite-volume Gibbs mean is additive under subtraction on bounded
continuous observables. -/
theorem continuous_compact_oriented_gibbsMeanReal_sub_bcf
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (F G : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.gibbsMeanReal (fun A => (F - G) A) =
      C.gibbsMeanReal (fun A => F A) - C.gibbsMeanReal (fun A => G A) := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsMeanReal
  simpa using
    (integral_sub
      (continuous_compact_oriented_bcf_integrable_gibbs_covariance_fluctuation C F)
      (continuous_compact_oriented_bcf_integrable_gibbs_covariance_fluctuation C G))

/-- The finite-volume Gibbs pairing is additive under subtraction in its left
bounded-continuous slot. -/
theorem continuous_compact_oriented_gibbsPairingReal_sub_left_bcf
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (F G O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.gibbsPairingReal (fun A => (F - G) A) (fun A => O A) =
      C.gibbsPairingReal (fun A => F A) (fun A => O A) -
        C.gibbsPairingReal (fun A => G A) (fun A => O A) := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsPairingReal
  simpa [sub_mul] using
    (integral_sub
      (continuous_compact_oriented_bcf_integrable_gibbs_covariance_fluctuation C (F * O))
      (continuous_compact_oriented_bcf_integrable_gibbs_covariance_fluctuation C (G * O)))

/-- The finite-volume Gibbs pairing is additive under subtraction in its right
bounded-continuous slot. -/
theorem continuous_compact_oriented_gibbsPairingReal_sub_right_bcf
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (F O P : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.gibbsPairingReal (fun A => F A) (fun A => (O - P) A) =
      C.gibbsPairingReal (fun A => F A) (fun A => O A) -
        C.gibbsPairingReal (fun A => F A) (fun A => P A) := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsPairingReal
  simpa [mul_sub] using
    (integral_sub
      (continuous_compact_oriented_bcf_integrable_gibbs_covariance_fluctuation C (F * O))
      (continuous_compact_oriented_bcf_integrable_gibbs_covariance_fluctuation C (F * P)))

/-- Gibbs covariance is additive under subtraction in its left bounded-continuous
slot. -/
theorem continuous_compact_oriented_gibbsCovarianceReal_sub_left_bcf
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (F G O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.gibbsCovarianceReal (fun A => (F - G) A) (fun A => O A) =
      C.gibbsCovarianceReal (fun A => F A) (fun A => O A) -
        C.gibbsCovarianceReal (fun A => G A) (fun A => O A) := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsCovarianceReal
  rw [continuous_compact_oriented_gibbsPairingReal_sub_left_bcf C F G O,
    continuous_compact_oriented_gibbsMeanReal_sub_bcf C F G]
  ring

/-- Gibbs covariance is additive under subtraction in its right bounded-continuous
slot. -/
theorem continuous_compact_oriented_gibbsCovarianceReal_sub_right_bcf
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (F O P : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.gibbsCovarianceReal (fun A => F A) (fun A => (O - P) A) =
      C.gibbsCovarianceReal (fun A => F A) (fun A => O A) -
        C.gibbsCovarianceReal (fun A => F A) (fun A => P A) := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsCovarianceReal
  rw [continuous_compact_oriented_gibbsPairingReal_sub_right_bcf C F O P,
    continuous_compact_oriented_gibbsMeanReal_sub_bcf C O P]
  ring

/-- Bounded-continuous one-link fluctuation `Q_e = I - P_e`. -/
noncomputable def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathFluctuationContinuousBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    BoundedContinuousFunction C.base.Configuration ℝ :=
  O - C.singleLinkConditionalExpectationContinuousBCF target O

@[simp] theorem continuous_compact_oriented_singleLinkHeatBathFluctuationContinuousBCF_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration) :
    C.singleLinkHeatBathFluctuationContinuousBCF target O A =
      O A - C.singleLinkConditionalExpectationContinuousBCF target O A := by
  rfl

/-- Every one-link heat-bath fluctuation has zero finite-volume Wilson Gibbs
mean. -/
theorem continuous_compact_oriented_gibbsMeanReal_singleLinkHeatBathFluctuationContinuousBCF_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.gibbsMeanReal
        (fun A => C.singleLinkHeatBathFluctuationContinuousBCF target O A) = 0 := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathFluctuationContinuousBCF
  rw [continuous_compact_oriented_gibbsMeanReal_sub_bcf C O
      (C.singleLinkConditionalExpectationContinuousBCF target O),
    continuous_compact_oriented_gibbsMeanReal_singleLinkConditionalExpectationContinuousBCF
      C target O]
  ring

/-- The one-link fluctuation `Q_e = I - P_e` is self-adjoint for the
finite-volume Wilson Gibbs covariance. -/
theorem continuous_compact_oriented_singleLinkHeatBathFluctuationContinuousBCF_gibbsCovariance_symm
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (F O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.gibbsCovarianceReal
        (fun A => C.singleLinkHeatBathFluctuationContinuousBCF target F A)
        (fun A => O A) =
      C.gibbsCovarianceReal
        (fun A => F A)
        (fun A => C.singleLinkHeatBathFluctuationContinuousBCF target O A) := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathFluctuationContinuousBCF
  rw [continuous_compact_oriented_gibbsCovarianceReal_sub_left_bcf C F
      (C.singleLinkConditionalExpectationContinuousBCF target F) O,
    continuous_compact_oriented_gibbsCovarianceReal_sub_right_bcf C F O
      (C.singleLinkConditionalExpectationContinuousBCF target O),
    continuous_compact_oriented_singleLinkConditionalExpectationContinuousBCF_gibbsCovariance_symm
      C target F O]

end

end MathlibAnalytic
end MGAP4D
