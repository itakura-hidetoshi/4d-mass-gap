import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairFixedBackgroundResponseResidualCoefficient
import Mathlib.Tactic

/-!
# Strict response-residual cutoff

PR #4844 proves that the volume-independent fixed-background response-residual
coefficient

  rhoResp(s,beta)
    = ofReal(qShell(s,beta)^2) * C_RMS(s,beta)

is finite on the canonical bidirectional-shell interval and vanishes exactly
at beta = 0.

This file records the missing scalar continuation fact.  Both factors are
continuous at zero coupling:

* qShell is already continuous at zero;
* the RMS target coefficient is built from the continuous half-barrier
  coefficient, ENNReal truncated subtraction/inversion, and exp(32 beta).

Hence rhoResp is continuous at zero as an ENNReal-valued function.  Since
rhoResp(s,0)=0<1, there is a strictly positive volume-independent coupling
interval, chosen inside the existing shell cutoff, on which

  rhoResp(s,beta) < 1.

No new response estimate, probability law, finite-volume constant, or
cardinality factor is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory Topology

noncomputable section

/-- The common fixed-background second-mean RMS target-majorant coefficient is
continuous at zero coupling. -/
theorem
    continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetMajorantCoefficient
    (s : ℝ) :
    ContinuousAt
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetMajorantCoefficient
        s)
      0 := by
  let c :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
      s
  have hc : ContinuousAt c 0 := by
    simpa [c] using
      continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
        s
  have hcSq : ContinuousAt (fun beta : ℝ => (c beta) ^ 2) 0 :=
    hc.pow 2
  have hcOfReal :
      ContinuousAt
        (fun beta : ℝ => ENNReal.ofReal ((c beta) ^ 2))
        0 :=
    ENNReal.continuous_ofReal.continuousAt.comp 0 hcSq
  have hGap :
      ContinuousAt
        (fun beta : ℝ =>
          (1 : ℝ≥0∞) - ENNReal.ofReal ((c beta) ^ 2))
        0 :=
    (ENNReal.continuous_sub_left ENNReal.one_ne_top).continuousAt.comp
      0 hcOfReal
  have hInv :
      ContinuousAt
        (fun beta : ℝ =>
          ((1 : ℝ≥0∞) - ENNReal.ofReal ((c beta) ^ 2))⁻¹)
        0 :=
    continuous_inv.continuousAt.comp 0 hGap
  have hExpSq :
      ContinuousAt
        (fun beta : ℝ => (Real.exp (32 * beta)) ^ 2)
        0 := by
    fun_prop
  have hExpOfReal :
      ContinuousAt
        (fun beta : ℝ =>
          ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2))
        0 :=
    ENNReal.continuous_ofReal.continuousAt.comp 0 hExpSq
  have hExpPlus :
      ContinuousAt
        (fun beta : ℝ =>
          ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) + 1)
        0 :=
    hExpOfReal.add continuousAt_const
  simpa [
    c,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetMajorantCoefficient] using
    hInv.mul hExpPlus

/-- The complete response-to-residual coefficient is continuous at zero
coupling. -/
theorem
    continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualCoefficient
    (s : ℝ) :
    ContinuousAt
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualCoefficient
        s)
      0 := by
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCoefficient
      s
  have hq : ContinuousAt q 0 := by
    simpa [q] using
      continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCoefficient
        s
  have hqSq : ContinuousAt (fun beta : ℝ => (q beta) ^ 2) 0 :=
    hq.pow 2
  have hqOfReal :
      ContinuousAt
        (fun beta : ℝ => ENNReal.ofReal ((q beta) ^ 2))
        0 :=
    ENNReal.continuous_ofReal.continuousAt.comp 0 hqSq
  have hTarget :=
    continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetMajorantCoefficient
      s
  simpa [
    q,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualCoefficient] using
    hqOfReal.mul hTarget

/-- Zero-coupling continuity produces a strictly positive interval, contained
in the existing shell cutoff, on which the response-residual coefficient is
strictly contractive. -/
theorem
    exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualStrictCutoff
    (s : ℝ) (hs : 8 < s) :
    ∃ couplingCutoff : ℝ,
      0 < couplingCutoff ∧
      couplingCutoff ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff
          s hs ∧
      ∀ beta : ℝ,
        0 ≤ beta →
        beta ≤ couplingCutoff →
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualCoefficient
              s beta < 1 := by
  let R :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualCoefficient
      s
  have hContinuous : ContinuousAt R 0 := by
    simpa [R] using
      continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualCoefficient
        s
  have hZero : R 0 = 0 := by
    simp [R]
  have hNear :
      ∀ᶠ beta : ℝ in 𝓝 0, R beta < (1 : ℝ≥0∞) :=
    hContinuous.eventually_lt continuousAt_const (by
      rw [hZero]
      exact zero_lt_one)
  obtain ⟨delta, hDelta, hBall⟩ :=
    Metric.mem_nhds_iff.mp hNear
  let shellCutoff :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff
      s hs
  let couplingCutoff := min (delta / 2) shellCutoff
  have hShellPos : 0 < shellCutoff := by
    simpa [shellCutoff] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff_pos
        s hs
  have hHalfDelta : 0 < delta / 2 := by
    positivity
  have hCutoffPos : 0 < couplingCutoff := by
    dsimp [couplingCutoff]
    exact lt_min hHalfDelta hShellPos
  refine ⟨couplingCutoff, hCutoffPos, ?_, ?_⟩
  · dsimp [couplingCutoff]
    exact min_le_right _ _
  · intro beta hbeta hbetaCutoff
    have hBetaHalfDelta :
        beta ≤ delta / 2 :=
      hbetaCutoff.trans (by
        dsimp [couplingCutoff]
        exact min_le_left _ _)
    have hBetaDelta : beta < delta := by
      linarith
    have hMemBall : beta ∈ Metric.ball (0 : ℝ) delta := by
      rw [Metric.mem_ball, Real.dist_eq]
      simpa [abs_of_nonneg hbeta] using hBetaDelta
    exact hBall hMemBall

/-- Canonical strict response-residual cutoff for a fixed scale s>8. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualStrictCutoff
    (s : ℝ) (hs : 8 < s) : ℝ :=
  Classical.choose
    (exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualStrictCutoff
      s hs)

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualStrictCutoff_pos
    (s : ℝ) (hs : 8 < s) :
    0 <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualStrictCutoff
        s hs :=
  (Classical.choose_spec
    (exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualStrictCutoff
      s hs)).1

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualStrictCutoff_le_shellCutoff
    (s : ℝ) (hs : 8 < s) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualStrictCutoff
        s hs ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff
        s hs :=
  (Classical.choose_spec
    (exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualStrictCutoff
      s hs)).2.1

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualStrictCutoff_spec
    (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualStrictCutoff
          s hs) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualCoefficient
        s beta < 1 :=
  (Classical.choose_spec
    (exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualStrictCutoff
      s hs)).2.2
    beta hbeta hcut

end

end MGAP4D.MathlibAnalytic
