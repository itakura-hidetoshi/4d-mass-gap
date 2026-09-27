import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairPinFreeBidirectionalShellCutoff
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairFixedBackgroundResponseAmplitude
import Mathlib.Tactic

/-!
# Fixed-background response amplitudes through the canonical pin-free Schur bound

PR #4836 gives, at each fixed outer boundary C,

  A_resp^C(source,target)
    <= K_pin(target,source) * U_target^C(target),

for the current-value response amplitudes.  PR #4840 supplies volume-uniform
row and column bounds for the same configuration-independent canonical pin-free
kernel and hence an L2 Schur contraction with coefficient qShell(s,beta) < 1.

The response assembler is transpose-oriented: target amplitudes propagate into
source coordinates through K_pin(target,source).  This file first records the
transpose Schur action of K_pin and then feeds the fixed-C response-amplitude
matrix into it.

For a link-indexed bounded observable family F_target the resulting estimate is

  sum_source (sum_target A_resp^C(source,target))^2
    <= qShell(s,beta)^2 * sum_target U_target^C(target)^2.

There is no source-cardinality factor, no response symmetry assumption, and no
source/target exchange in the physical kernel.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance fixedBackgroundResponseAmplitudeSchurSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance fixedBackgroundResponseAmplitudeSchurSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The canonical pin-free kernel has the same volume-uniform L2 Schur bound
for its transpose action. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_transpose_action_sq_sum_le_bidirectionalShellCoefficient_sq
    (H N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff
          s hs)
    (vector : PeriodicHypercubicEvenSpatialSliceLink H → ℝ) :
    (∑ source,
      (∑ target,
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
          H beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
            H N hN beta hbeta)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
            H N hN beta hbeta)).influence target source *
          vector target) ^ 2) ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCoefficient
        s beta) ^ 2 *
        ∑ target, vector target ^ 2 := by
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
      H beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
        H N hN beta hbeta)
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCoefficient
      s beta
  have hStrictCut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s :=
    hcut.trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff_le_strictPhysicalSweepCutoff
        s hs)
  have hHalfCut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s :=
    hStrictCut.trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff_le_halfBarrierCutoff
        s)
  have hq0 : 0 ≤ q := by
    simpa [
      q,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCoefficient] using
      mul_nonneg
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightBootstrapEnvelopePinFreeCoefficient_nonneg
          s beta hbeta hHalfCut)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMassMajorant_nonneg
          s hs)
  have hRow :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        ∑ source, K.influence target source ≤ q := by
    intro target
    simpa [K, q] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_rowSum_le_bidirectionalShellCoefficient
        H N hN s hs beta hbeta hcut target
  have hColumn :
      ∀ source : PeriodicHypercubicEvenSpatialSliceLink H,
        ∑ target, K.influence target source ≤ q := by
    intro source
    simpa [K, q] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_columnSum_le_bidirectionalShellCoefficient
        H N hN s hs beta hbeta hcut source
  have hSchur :=
    FiniteNonnegativeSchur.action_sq_sum_le_row_mul_column
      (fun source target => K.influence target source)
      (fun source target => K.influence_nonneg target source)
      q q hq0
      (by
        intro source
        simpa using hColumn source)
      (by
        intro target
        simpa using hRow target)
      vector
  simpa [K, q, pow_two] using hSchur

/-- At fixed C, the complete source-indexed sum of target response amplitudes
is controlled in L2 by the target-amplitude profile with the same qShell
coefficient.  The observable family is target-indexed, matching the canonical
assembled-state orientation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedFixedBackgroundResponseAmplitude_sum_sq_le_bidirectionalShellCoefficient_sq_mul_targetAmplitude_sq_sum
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
    (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseAmplitudeMatrix
          H N hN beta hbeta C distinguishedSource
          (F target) (hF target) (bound target) (hbound target)
          source target) ^ 2) ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCoefficient
        s beta) ^ 2 *
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetAmplitude
            H N hN s beta hbeta C target (F target) ^ 2 := by
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
      H beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
        H N hN beta hbeta)
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCoefficient
      s beta
  let U :=
    fun target : PeriodicHypercubicEvenSpatialSliceLink H =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetAmplitude
        H N hN s beta hbeta C target (F target)
  let A :=
    fun source target : PeriodicHypercubicEvenSpatialSliceLink H =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseAmplitudeMatrix
        H N hN beta hbeta C distinguishedSource
        (F target) (hF target) (bound target) (hbound target)
        source target
  have hStrictCut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s :=
    hcut.trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff_le_strictPhysicalSweepCutoff
        s hs)
  have hEntry :
      ∀ source target : PeriodicHypercubicEvenSpatialSliceLink H,
        A source target ≤ K.influence target source * U target := by
    intro source target
    simpa [A, K, U] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseAmplitudeMatrix_le_canonicalPinFree_mul_targetAmplitude
        N hN s (by linarith) beta hbeta hStrictCut H C distinguishedSource
        source target (F target) (hF target) (bound target) (hbound target)
  have hA0 :
      ∀ source target : PeriodicHypercubicEvenSpatialSliceLink H,
        0 ≤ A source target := by
    intro source target
    simpa [A] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseAmplitudeMatrix_nonneg
        H N hN beta hbeta C distinguishedSource
        (F target) (hF target) (bound target) (hbound target)
        source target
  have hU0 :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        0 ≤ U target := by
    intro target
    simpa [U] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetAmplitude_nonneg
        H N hN s beta hbeta C target (F target)
  have hSq :
      ∀ source : PeriodicHypercubicEvenSpatialSliceLink H,
        (∑ target, A source target) ^ 2 ≤
          (∑ target, K.influence target source * U target) ^ 2 := by
    intro source
    have hSum :
        (∑ target, A source target) ≤
          ∑ target, K.influence target source * U target := by
      apply Finset.sum_le_sum
      intro target htarget
      exact hEntry source target
    have hLeft0 : 0 ≤ ∑ target, A source target := by
      exact Finset.sum_nonneg (fun target _ => hA0 source target)
    have hRight0 :
        0 ≤ ∑ target, K.influence target source * U target := by
      exact Finset.sum_nonneg (fun target _ =>
        mul_nonneg (K.influence_nonneg target source) (hU0 target))
    exact (sq_le_sq₀ hLeft0 hRight0).2 hSum
  have hSchur :
      (∑ source,
        (∑ target, K.influence target source * U target) ^ 2) ≤
        q ^ 2 * ∑ target, U target ^ 2 := by
    simpa [K, q, U] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_transpose_action_sq_sum_le_bidirectionalShellCoefficient_sq
        H N hN s hs beta hbeta hcut U
  have hMatrix :
      (∑ source, (∑ target, A source target) ^ 2) ≤
        ∑ source, (∑ target, K.influence target source * U target) ^ 2 := by
    exact Finset.sum_le_sum (fun source _ => hSq source)
  exact
    (by
      simpa [A, K, U, q] using hMatrix.trans hSchur)

end

end MGAP4D.MathlibAnalytic
