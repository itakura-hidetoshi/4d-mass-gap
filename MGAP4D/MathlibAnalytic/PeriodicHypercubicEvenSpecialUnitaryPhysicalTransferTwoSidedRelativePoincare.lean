import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedConstantLineConvergence
import MGAP4D.MathlibAnalytic.RealHilbertProjectionSweepInitialResidualControl
import Mathlib.Tactic

/-!
# Two-sided relative Poincare from the actual tagged one-link sweep

PR #4970 identifies the limit of the complete tagged one-link sweep with the
orthogonal projection onto the intrinsic joint constant line.

This file closes the quantitative renewal step.

First, the bounded-core two-sided one-step forcing theorem is extended to every
genuine joint L2 vector by density and closedness.  The SAME target-first /
source-second two-boundary ordered kernel is retained.

Then the generic source-profile / one-sided Schur argument gives, for any
duplicate-free tagged-link order,

  (1-Q)^2 * pathLoss <= sum_e ||f - P_e f||^2.

For the complete canonical sweep, #4969 supplies geometric loss contraction and
#4970 supplies convergence to the constant-line projection.  Exact Pythagoras
and the renewal tail lemma therefore give

  (1-eta) ||f - Pi_const f||^2 <= pathLoss,

with eta = (Q/(1-Q))^2.

The exact scalar cancellation

  (1-Q)^2 (1-eta) = 1 - 2Q

finally yields

  (1-2Q) ||f - Pi_const f||^2
    <= sum_e ||f - P_e f||^2.

The coefficient is positive on the existing #4969 loss-contraction cutoff.
No bounded-core premise, source-count factor, or volume factor remains in the
coefficient.  The right-hand side is still the UNNORMALIZED tagged one-link
energy; the volume-safe link-to-color comparison remains the next unit.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter
open scoped BigOperators Topology InnerProductSpace InnerProduct

noncomputable section

local instance twoSidedRelativePoincareSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The actual two-sided source-update forcing estimate extends from the dense
bounded-concrete core to every genuine joint L2 vector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_sourceUpdate_targetResidual_norm_le_add_sourceResidual_allL2
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 8 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossContractionCutoff
          s hs)
    (source target : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    let P :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
        H N hN beta hbeta
    let K :=
      GroundStateSourceFixedPairEnergy.twoBoundaryOrderedKernel
        H N hN beta hbeta s
    ‖P source f - P target (P source f)‖ ≤
      ‖f - P target f‖ + K target source * ‖f - P source f‖ := by
  dsimp only
  let E :=
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
      H N hN beta hbeta
  let K :=
    GroundStateSourceFixedPairEnergy.twoBoundaryOrderedKernel
      H N hN beta hbeta s
  by_cases hEq : target = source
  · subst target
    have hIdem :
        P source (P source f) = P source f := by
      simpa only [P, ContinuousLinearMap.comp_apply] using
        congrArg
          (fun T : E →L[ℝ] E => T f)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2_idempotent
            H N hN beta hbeta source)
    rw [hIdem, sub_self, norm_zero]
    exact
      add_nonneg
        (norm_nonneg _)
        (mul_nonneg
          (GroundStateSourceFixedPairEnergy.twoBoundaryOrderedKernel_nonneg
            H N hN beta hbeta s source source)
          (norm_nonneg _))
  · let A : E →L[ℝ] E :=
      P source - (P target).comp (P source)
    let Rt : E →L[ℝ] E :=
      ContinuousLinearMap.id ℝ E - P target
    let Rs : E →L[ℝ] E :=
      ContinuousLinearMap.id ℝ E - P source
    let good : Set E :=
      {g | ‖A g‖ ≤ ‖Rt g‖ + K target source * ‖Rs g‖}
    have hClosed : IsClosed good := by
      exact
        isClosed_le
          A.continuous.norm
          (Rt.continuous.norm.add
            (continuous_const.mul Rs.continuous.norm))
    have hCoreSub :
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
            H N hN beta hbeta ⊆ good := by
      intro g hg
      have hStrict :
          beta ≤
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
              s := by
        exact
          (((hcut.trans
              (GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossContractionCutoff_le_schurCutoff
                s hs)).trans
              (GroundStateSourceFixedPairEnergy.twoBoundaryOrderedSchurCutoff_le_jointLeakageSchurCutoff
                s hs))).trans
            (GroundStateSourceFixedPairEnergy.jointLeakageSchurCutoff_le_strictPhysicalSweepCutoff
              s hs))
      have hCross :
          beta <
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBetaThreshold :=
        GroundStateSourceFixedPairEnergy.beta_lt_crossThreshold_of_le_twoBoundaryOrderedLossContractionCutoff
          s hs beta hcut
      have h :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_sourceUpdate_targetResidual_norm_le_add_sourceResidual
          H N hN beta hbeta s (by linarith) hStrict hCross
          source target hEq g hg
      simpa [good, A, Rt, Rs, P, K,
        ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply] using h
    have hDense :
        Dense
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
            H N hN beta hbeta) :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore_dense
        H N hN beta hbeta
    have hAll :
        closure
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
              H N hN beta hbeta) ⊆ good :=
      closure_minimal hCoreSub hClosed
    have hf : f ∈ good := by
      apply hAll
      rw [hDense.closure_eq]
      exact Set.mem_univ f
    simpa [good, A, Rt, Rs, P, K,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply] using hf

/-- Any duplicate-free tagged-link trajectory has exact path loss controlled by
the ORIGINAL tagged one-link residual energy with the same two-boundary Schur
coefficient.  No completeness hypothesis is needed for this step. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_pathLoss_controlled_by_initialResidual
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 8 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossContractionCutoff
          s hs)
    (sources : List (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H))
    (hNodup : sources.Nodup)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    let P :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
        H N hN beta hbeta
    let Q :=
      GroundStateSourceFixedPairEnergy.twoBoundaryOrderedSchurCoefficient s beta
    (1 - Q) ^ 2 *
        realHilbertProjectionSweepPathLoss P sources f ≤
      ∑ e : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H,
        ‖f - P e f‖ ^ 2 := by
  dsimp only
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
      H N hN beta hbeta
  let matrix :=
    GroundStateSourceFixedPairEnergy.twoBoundaryOrderedKernel
      H N hN beta hbeta s
  let profile :=
    realHilbertProjectionSweepSourceResidualProfile P sources f
  let initial :
      PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H → ℝ :=
    fun e => ‖f - P e f‖
  let Q :=
    GroundStateSourceFixedPairEnergy.twoBoundaryOrderedSchurCoefficient s beta
  have hQ :=
    GroundStateSourceFixedPairEnergy.twoBoundaryOrderedSchurCoefficient_nonneg_lt_half
      s hs beta hbeta hcut
  have hMatrix :
      ∀ target source, 0 ≤ matrix target source := by
    intro target source
    exact
      GroundStateSourceFixedPairEnergy.twoBoundaryOrderedKernel_nonneg
        H N hN beta hbeta s target source
  have hStep :
      ∀ source target
        (x :
          PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
            H N hN beta hbeta),
        ‖P source x - P target (P source x)‖ ≤
          ‖x - P target x‖ + matrix target source * ‖x - P source x‖ := by
    intro source target x
    simpa [P, matrix] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_sourceUpdate_targetResidual_norm_le_add_sourceResidual_allL2
        H N hN s hs beta hbeta hcut source target x
  have hOneSided :
      ∀ target,
        profile target ≤
          initial target +
            ∑ source, matrix target source * profile source := by
    intro target
    have h :=
      realHilbertProjectionSweepSourceResidualProfile_le_budget_add_initial
        P
        (fun source target => matrix target source)
        (fun source target => hMatrix target source)
        hStep
        sources f hNodup target
    rw [
      realHilbertProjectionSweepTargetResidualForcingBudget_eq_weightedSourceProfile]
      at h
    exact h.trans_eq (add_comm _ _)
  have hSchur :
      ∀ v : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H → ℝ,
        (∑ target,
          (∑ source, matrix target source * v source) ^ 2) ≤
            Q ^ 2 * ∑ source, v source ^ 2 := by
    intro v
    have hJoint :
        beta ≤ GroundStateSourceFixedPairEnergy.jointLeakageSchurCutoff s hs :=
      (hcut.trans
        (GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossContractionCutoff_le_schurCutoff
          s hs)).trans
        (GroundStateSourceFixedPairEnergy.twoBoundaryOrderedSchurCutoff_le_jointLeakageSchurCutoff
          s hs)
    simpa [matrix, Q] using
      GroundStateSourceFixedPairEnergy.twoBoundaryOrderedKernel_action_sq_sum_le
        H N hN s hs beta hbeta hJoint v
  have hEnergy :=
    FiniteSchurOneSidedProfile.global_energy_coercive
      matrix Q hQ.1 (lt_trans hQ.2 (by norm_num))
      hMatrix hSchur
      profile initial
      (fun e =>
        realHilbertProjectionSweepSourceResidualProfile_nonneg
          P sources f e)
      (fun e => norm_nonneg _)
      hOneSided
  have hProfile :
      (∑ e : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H,
        profile e ^ 2) =
        realHilbertProjectionSweepPathLoss P sources f :=
    realHilbertProjectionSweepSourceResidualProfile_sq_sum_eq_pathLoss
      P sources f hNodup
  rw [hProfile] at hEnergy
  simpa [initial, Q] using hEnergy

/-- Exact Pythagoras for one complete canonical two-sided sweep relative to the
intrinsic constant-line projection. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_constantProjection_pythagoras
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    let P :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
        H N hN beta hbeta
    let sources :=
      ((Finset.univ :
        Finset (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H)).toList)
    let B :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection
        H N hN beta hbeta
    let S := realHilbertProjectionSweep P sources
    ‖f - B f‖ ^ 2 =
      realHilbertProjectionSweepPathLoss P sources f +
        ‖S f - B (S f)‖ ^ 2 := by
  dsimp only
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
      H N hN beta hbeta
  let sources :=
    ((Finset.univ :
      Finset (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H)).toList)
  let C :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
      H N hN beta hbeta
  let B :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection
      H N hN beta hbeta
  let S := realHilbertProjectionSweep P sources
  have hBid : B.comp B = B := by
    apply ContinuousLinearMap.ext
    intro x
    change C.starProjection (C.starProjection x) = C.starProjection x
    exact
      Submodule.starProjection_eq_self_iff.mpr
        (C.starProjection_apply_mem x)
  have hBsymm :
      ∀ x y, inner ℝ (B x) y = inner ℝ x (B y) := by
    intro x y
    exact Submodule.inner_starProjection_left_eq_right C x y
  have hFirst :=
    realHilbertProjection_residual_norm_sq B hBid hBsymm f
  have hSecond :=
    realHilbertProjection_residual_norm_sq B hBid hBsymm (S f)
  have hAbsorb :
      B (S f) = B f := by
    simpa [P, sources, B, S,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkFullSweepVector] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection_absorb_twoSidedFullSweep
        H N hN beta hbeta f
  rw [hAbsorb] at hSecond
  have hLoss :=
    realHilbertProjectionSweep_norm_sq_loss
      P
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2_idempotent
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2_symmetric
        H N hN beta hbeta)
      sources f
  change ‖f - B f‖ ^ 2 =
    realHilbertProjectionSweepPathLoss P sources f +
      ‖S f - B (S f)‖ ^ 2
  rw [hAbsorb]
  nlinarith

/-- The first complete-sweep path loss controls the entire constant-centered
joint variance with coefficient 1-eta.  The tail is discharged by #4970's
actual convergence theorem. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_pathLoss_ge_one_sub_lossRatio_mul_constantVariance
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 8 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossContractionCutoff
          s hs)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    let P :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
        H N hN beta hbeta
    let sources :=
      ((Finset.univ :
        Finset (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H)).toList)
    let B :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection
        H N hN beta hbeta
    (1 - GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossRatio s beta) *
        ‖f - B f‖ ^ 2 ≤
      realHilbertProjectionSweepPathLoss P sources f := by
  dsimp only
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
      H N hN beta hbeta
  let sources :=
    ((Finset.univ :
      Finset (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H)).toList)
  let S :=
    realHilbertProjectionSweep P sources
  let B :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection
      H N hN beta hbeta
  let eta :=
    GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossRatio s beta
  let D : ℕ → ℝ :=
    fun n => ‖S^[n] f - B (S^[n] f)‖ ^ 2
  let losses : ℕ → ℝ :=
    fun n =>
      realHilbertProjectionSweepPathLoss P sources (S^[n] f)
  have hLimit :
      Tendsto (fun n : ℕ => S^[n] f) atTop (𝓝 (B f)) := by
    simpa [P, sources, S, B] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_iterates_tendsto_constantProjection
        H N hN s hs beta hbeta hcut f
  have hIdem : B (B f) = B f := by
    let C :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
        H N hN beta hbeta
    change C.starProjection (C.starProjection f) = C.starProjection f
    exact
      Submodule.starProjection_eq_self_iff.mpr
        (C.starProjection_apply_mem f)
  have hTail : Tendsto D atTop (𝓝 0) := by
    have hDiff :=
      hLimit.sub (((B).continuous.tendsto (B f)).comp hLimit)
    simpa only [
      D, hIdem, sub_self, norm_zero,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      hDiff.norm.pow 2
  have hRenew : ∀ n : ℕ, D n = losses n + D (n + 1) := by
    intro n
    simpa only [
      D, losses, Function.iterate_succ_apply'] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_constantProjection_pythagoras
        H N hN beta hbeta (S^[n] f)
  have hLoss :
      ∀ n : ℕ, losses (n + 1) ≤ eta * losses n := by
    intro n
    dsimp only [losses]
    rw [Function.iterate_succ_apply']
    simpa [P, sources, S, eta] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_pathLoss_le_lossRatio_mul_allL2
        H N hN s hs beta hbeta hcut (S^[n] f)
  simpa only [
    D, losses, eta, Function.iterate_zero, id_eq] using
    RenewalTail.current_loss_controls_energy_of_tendsto_zero
      D losses eta hRenew hLoss hTail

/-- Uniform two-sided relative Poincare on the entire genuine joint L2 carrier.
The center is the intrinsic constant-line orthogonal projection.

The coefficient is exactly 1-2Q and is strictly positive on the SAME #4969
loss-contraction cutoff.  The right-hand side is the unnormalized tagged
one-link residual energy. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_relativePoincare
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 8 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossContractionCutoff
          s hs)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    let P :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
        H N hN beta hbeta
    let B :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection
        H N hN beta hbeta
    (1 - 2 *
        GroundStateSourceFixedPairEnergy.twoBoundaryOrderedSchurCoefficient
          s beta) *
        ‖f - B f‖ ^ 2 ≤
      ∑ e : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H,
        ‖f - P e f‖ ^ 2 := by
  dsimp only
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
      H N hN beta hbeta
  let B :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection
      H N hN beta hbeta
  let sources :=
    ((Finset.univ :
      Finset (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H)).toList)
  let q :=
    GroundStateSourceFixedPairEnergy.twoBoundaryOrderedSchurCoefficient s beta
  let eta :=
    GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossRatio s beta
  have hMargin :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_pathLoss_ge_one_sub_lossRatio_mul_constantVariance
      H N hN s hs beta hbeta hcut f
  have hInitial :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_pathLoss_controlled_by_initialResidual
      H N hN s hs beta hbeta hcut
      sources (Finset.nodup_toList _) f
  have hQ :=
    GroundStateSourceFixedPairEnergy.twoBoundaryOrderedSchurCoefficient_nonneg_lt_half
      s hs beta hbeta hcut
  have hDen : 1 - q ≠ 0 := by
    dsimp [q]
    linarith [hQ.2]
  have hEtaMul :
      (1 - q) ^ 2 * eta = q ^ 2 := by
    change
      (1 - q) ^ 2 * (q / (1 - q)) ^ 2 = q ^ 2
    rw [div_pow]
    field_simp [hDen]
  have hCoeff :
      (1 - q) ^ 2 * (1 - eta) = 1 - 2 * q := by
    nlinarith [hEtaMul]
  change
    (1 - 2 * q) * ‖f - B f‖ ^ 2 ≤
      ∑ e : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H,
        ‖f - P e f‖ ^ 2
  calc
    (1 - 2 * q) * ‖f - B f‖ ^ 2 =
        (1 - q) ^ 2 *
          ((1 - eta) * ‖f - B f‖ ^ 2) := by
      rw [← mul_assoc, hCoeff]
    _ ≤
        (1 - q) ^ 2 *
          realHilbertProjectionSweepPathLoss P sources f :=
      mul_le_mul_of_nonneg_left
        (by simpa [P, sources, B, eta] using hMargin)
        (sq_nonneg _)
    _ ≤
        ∑ e : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H,
          ‖f - P e f‖ ^ 2 := by
      simpa [P, sources, q] using hInitial

theorem
    GroundStateSourceFixedPairEnergy.twoBoundaryOrderedRelativePoincareCoefficient_pos
    (s : ℝ)
    (hs : 8 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossContractionCutoff
          s hs) :
    0 <
      1 - 2 *
        GroundStateSourceFixedPairEnergy.twoBoundaryOrderedSchurCoefficient
          s beta := by
  linarith [
    (GroundStateSourceFixedPairEnergy.twoBoundaryOrderedSchurCoefficient_nonneg_lt_half
      s hs beta hbeta hcut).2]

end

end MathlibAnalytic
end MGAP4D
