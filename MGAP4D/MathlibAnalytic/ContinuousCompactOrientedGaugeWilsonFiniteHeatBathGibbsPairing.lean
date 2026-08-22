import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonFiniteHeatBathVariationPropagation
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathPairing
import Mathlib.Tactic

/-!
# Gibbs pairing invariance for finite current heat-bath schedules

The current compact Wilson carrier already has:

* exact finite ordered heat-bath kernels and their bounded-continuous Feller action;
* exact Gibbs stationarity of every such finite kernel;
* symmetry of each one-link heat-bath projection for the Gibbs pairing.

For static covariance arguments, stationarity alone is not enough to replace a
right observable by its heat-bath evolution inside a product.  The missing
identity is the conditional-expectation pairing law: if the left observable is
constant on every link fiber updated by a prescribed finite schedule, then the
whole finite heat-bath action can be removed from the right factor without
changing the Gibbs pairing.

This file proves that identity first for the closed bounded-continuous Feller
representative and then transfers it pointwise to the actual finite heat-bath
kernel expectation.

This is finite-volume Gibbs/heat-bath algebra only.  No covariance decay,
continuum clustering, Euclidean-time identification, positive physical mass,
OS Hamiltonian gap, or uniform factorial-continuum Dobrushin threshold is
asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

private theorem continuous_compact_oriented_bcf_abs_le_norm_pairing
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration) :
    |O A| ≤ ‖O‖ := by
  simpa [Real.norm_eq_abs] using O.norm_coe_le_norm A

private theorem
    continuous_compact_oriented_singleLinkConditionalExpectationContinuousBCF_coe_eq_projection
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    (fun A : C.base.Configuration =>
      C.singleLinkConditionalExpectationContinuousBCF target O A) =
      C.singleLinkHeatBathProjection target (fun A => O A) := by
  funext A
  rw [continuous_compact_oriented_singleLinkConditionalExpectationContinuousBCF_apply]
  rfl

/-- If the left bounded-continuous observable is constant on every physical
link fiber updated by a finite ordered heat-bath schedule, then the finite
Feller action on the right factor leaves the Gibbs pairing unchanged. -/
theorem continuous_compact_oriented_gibbsPairing_finiteSingleLinkHeatBathContinuousBCF_eq_of_left_offLinkFiberConstant
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (targets : List C.base.geometry.Edge)
    (F O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hFiber : ∀ target ∈ targets,
      C.base.OffLinkFiberConstant target (fun A => F A)) :
    C.gibbsPairingReal (fun A => F A)
        (fun A => C.finiteSingleLinkHeatBathContinuousBCF targets O A) =
      C.gibbsPairingReal (fun A => F A) (fun A => O A) := by
  induction targets with
  | nil =>
      rfl
  | cons target targets ih =>
      let G : BoundedContinuousFunction C.base.Configuration ℝ :=
        C.finiteSingleLinkHeatBathContinuousBCF targets O
      have hTarget :
          C.base.OffLinkFiberConstant target (fun A => F A) :=
        hFiber target (by simp)
      have hTail : ∀ e ∈ targets,
          C.base.OffLinkFiberConstant e (fun A => F A) := by
        intro e he
        exact hFiber e (by simp [he])
      have hPair :=
        continuous_compact_oriented_singleLinkHeatBathProjection_gibbsPairing_symm
          C target (fun A => F A) (fun A => G A)
          F.continuous.stronglyMeasurable G.continuous.stronglyMeasurable
          ‖F‖ ‖G‖ (norm_nonneg _) (norm_nonneg _)
          (fun A => continuous_compact_oriented_bcf_abs_le_norm_pairing F A)
          (fun A => continuous_compact_oriented_bcf_abs_le_norm_pairing G A)
      have hFix :
          C.singleLinkHeatBathProjection target (fun A => F A) =
            (fun A => F A) :=
        continuous_compact_oriented_singleLinkHeatBathProjection_fixes
          C target (fun A => F A) hTarget
      have hProjection :
          (fun A : C.base.Configuration =>
            C.singleLinkConditionalExpectationContinuousBCF target G A) =
            C.singleLinkHeatBathProjection target (fun A => G A) :=
        continuous_compact_oriented_singleLinkConditionalExpectationContinuousBCF_coe_eq_projection
          C target G
      rw [continuous_compact_oriented_finiteSingleLinkHeatBathContinuousBCF_cons]
      change
        C.gibbsPairingReal (fun A => F A)
            (fun A => C.singleLinkConditionalExpectationContinuousBCF target G A) =
          C.gibbsPairingReal (fun A => F A) (fun A => O A)
      rw [hProjection]
      rw [← hPair, hFix]
      exact ih hTail

/-- The same pairing invariance holds for the actual finite heat-bath-kernel
expectation, using the exact pointwise equality with the Feller representative. -/
theorem continuous_compact_oriented_gibbsPairing_finiteSingleLinkHeatBathExpectationBCF_eq_of_left_offLinkFiberConstant
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (targets : List C.base.geometry.Edge)
    (F O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hFiber : ∀ target ∈ targets,
      C.base.OffLinkFiberConstant target (fun A => F A)) :
    C.gibbsPairingReal (fun A => F A)
        (fun A => C.finiteSingleLinkHeatBathExpectationBCF targets O A) =
      C.gibbsPairingReal (fun A => F A) (fun A => O A) := by
  calc
    C.gibbsPairingReal (fun A => F A)
        (fun A => C.finiteSingleLinkHeatBathExpectationBCF targets O A) =
      C.gibbsPairingReal (fun A => F A)
        (fun A => C.finiteSingleLinkHeatBathContinuousBCF targets O A) := by
          unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsPairingReal
          apply integral_congr_ae
          filter_upwards [] with A
          rw [continuous_compact_oriented_finiteSingleLinkHeatBathContinuousBCF_eq_expectationBCF]
    _ = C.gibbsPairingReal (fun A => F A) (fun A => O A) :=
      continuous_compact_oriented_gibbsPairing_finiteSingleLinkHeatBathContinuousBCF_eq_of_left_offLinkFiberConstant
        C targets F O hFiber

end

end MathlibAnalytic
end MGAP4D
