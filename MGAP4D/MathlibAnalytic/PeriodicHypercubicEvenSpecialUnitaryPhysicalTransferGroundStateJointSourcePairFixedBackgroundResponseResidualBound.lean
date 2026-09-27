import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairFixedBackgroundResponseAmplitudeSchur
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairFixedBackgroundTargetAmplitudeResidualSum
import Mathlib.Tactic

/-!
# Fixed-background response amplitudes bounded by genuine target residual energy

PR #4841 closes the finite-volume transpose Schur step for the fixed-C
response-amplitude matrix:

  sum_source (sum_target A_resp^C(source,target))^2
    <= qShell(s,beta)^2 * sum_target U_target^C(target)^2.

PR #4842 identifies the target-amplitude energy exactly, after ENNReal.ofReal,
with a common scalar coefficient times the sum of genuine target
kernel-section residual energies.

This file composes those two statements without changing probability laws or
introducing any finite-cardinality factor.  The resulting fixed-C estimate is

  ofReal(sum_source (sum_target A_resp^C(source,target))^2)
    <= rhoResp(s,beta)
       * sum_target E_target(C,target),

with

  rhoResp(s,beta)
    = ofReal(qShell(s,beta)^2) * C_RMS(s,beta).

No integration over C is performed here.  That outer vacuum step remains
separate.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance fixedBackgroundResponseResidualBoundSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance fixedBackgroundResponseResidualBoundSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Combined response-to-residual ENNReal coefficient. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualCoefficient
    (s beta : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCoefficient
        s beta) ^ 2) *
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetMajorantCoefficient
      s beta

/-- At fixed outer boundary C, the complete source-summed response-amplitude
energy is bounded by the genuine target residual-energy sum with the
volume-independent combined scalar coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedFixedBackgroundResponseAmplitude_sum_sq_ofReal_le_responseResidualCoefficient_mul_targetResidualEnergy_sum
    (N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff
          s hs)
    (H : ℕ)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      PeriodicHypercubicEvenSpatialSliceLink H →
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : ∀ e, StronglyMeasurable (F e))
    (bound : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hbound : ∀ e z, ‖F e z‖ ≤ bound e) :
    ENNReal.ofReal
      (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
        (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseAmplitudeMatrix
            H N hN beta hbeta C distinguishedSource
            (F target) (hF target) (bound target) (hbound target)
            source target) ^ 2) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualCoefficient
          s beta *
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy
            H N hN beta hbeta C target (F target) := by
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCoefficient
      s beta
  let U :=
    fun target : PeriodicHypercubicEvenSpatialSliceLink H =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetAmplitude
        H N hN s beta hbeta C target (F target)
  have hStrictCut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s :=
    hcut.trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff_le_strictPhysicalSweepCutoff
        s hs)
  have hReal :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedFixedBackgroundResponseAmplitude_sum_sq_le_bidirectionalShellCoefficient_sq_mul_targetAmplitude_sq_sum
      N hN s hs beta hbeta hcut H C distinguishedSource
      F hF bound hbound
  have hENN :
      ENNReal.ofReal
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseAmplitudeMatrix
              H N hN beta hbeta C distinguishedSource
              (F target) (hF target) (bound target) (hbound target)
              source target) ^ 2) ≤
        ENNReal.ofReal
          (q ^ 2 * ∑ target : PeriodicHypercubicEvenSpatialSliceLink H, U target ^ 2) := by
    simpa [q, U] using ENNReal.ofReal_le_ofReal hReal
  calc
    ENNReal.ofReal
      (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
        (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseAmplitudeMatrix
            H N hN beta hbeta C distinguishedSource
            (F target) (hF target) (bound target) (hbound target)
            source target) ^ 2) ≤
        ENNReal.ofReal
          (q ^ 2 * ∑ target : PeriodicHypercubicEvenSpatialSliceLink H, U target ^ 2) :=
      hENN
    _ =
        ENNReal.ofReal (q ^ 2) *
          ENNReal.ofReal
            (∑ target : PeriodicHypercubicEvenSpatialSliceLink H, U target ^ 2) := by
      rw [ENNReal.ofReal_mul (sq_nonneg q)]
    _ =
        ENNReal.ofReal (q ^ 2) *
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetMajorantCoefficient
              s beta *
            ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy
                H N hN beta hbeta C target (F target)) := by
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedFixedBackgroundSecondMeanRMSTargetAmplitude_sq_sum_ofReal_eq_coefficient_mul_targetResidualEnergy_sum
          N hN s (by linarith) beta hbeta hStrictCut H C
          F hF bound hbound]
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualCoefficient
          s beta *
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy
            H N hN beta hbeta C target (F target) := by
      simp [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualCoefficient,
        q, mul_assoc]

end

end MGAP4D.MathlibAnalytic
