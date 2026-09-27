import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairFixedBackgroundResponseResidualBound
import Mathlib.Tactic

/-!
# Finiteness of the fixed-background response-to-residual coefficient

PR #4843 isolates the volume-independent ENNReal coefficient

  rhoResp(s,beta)
    = ofReal(qShell(s,beta)^2) * C_RMS(s,beta)

in the fixed-C response-amplitude estimate.

For the next outer-vacuum integration step it is useful to record explicitly
that both C_RMS and rhoResp are finite on the already-existing high-temperature
intervals.  No new cutoff is introduced.

We also record rhoResp(s,0)=0.  This makes the decoupled endpoint transparent
and will be useful if a later scalar optimization chooses to shrink the
interval further.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

/-- The common fixed-background target-majorant coefficient is finite on the
strict physical-sweep interval. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetMajorantCoefficient_ne_top
    (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetMajorantCoefficient
        s beta ≠ ⊤ := by
  let c : ℝ≥0∞ :=
    ENNReal.ofReal
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
        s beta) ^ 2)
  let gap : ℝ≥0∞ := 1 - c
  have hc : c < 1 := by
    simpa [c] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient_sq_ofReal_lt_one_of_strictPhysicalSweepCutoff
        s beta hbeta hcut
  have hGapPos : 0 < gap := by
    simpa [gap] using (tsub_pos_iff_lt.mpr hc)
  have hGapZero : gap ≠ 0 := ne_of_gt hGapPos
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetMajorantCoefficient
  change
    gap⁻¹ * (ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) + 1) ≠ ⊤
  apply ENNReal.mul_ne_top
  · exact ENNReal.inv_ne_top.2 hGapZero
  · exact
      ENNReal.add_ne_top.2
        ⟨ENNReal.ofReal_ne_top, ENNReal.one_ne_top⟩

/-- The combined response-to-residual coefficient is finite on the shell
cutoff from PR #4840. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualCoefficient_ne_top
    (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff
          s hs) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualCoefficient
        s beta ≠ ⊤ := by
  have hStrictCut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s :=
    hcut.trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff_le_strictPhysicalSweepCutoff
        s hs)
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualCoefficient
  exact
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetMajorantCoefficient_ne_top
        s (by linarith) beta hbeta hStrictCut)

/-- At zero coupling the combined response-to-residual coefficient vanishes
exactly. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualCoefficient_zero
    (s : ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualCoefficient
        s 0 = 0 := by
  simp [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualCoefficient]

end

end MGAP4D.MathlibAnalytic
