import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFixedRightTargetRatioNStepTerminalLeftVariationMass
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance fixedRightTargetIndexedResponseFamilySpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Remote fixed-right response column with independently chosen SU(N) test
values at each remote target.  This is the quantifier shape required before
taking targetwise worst cases: there is no common global tuple
`g₁, g₂, h, k` shared by all remote targets. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTargetIndexedRemoteResponseColumn
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source distinguishedTarget : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₁ g₂ h k :
      PeriodicHypercubicEvenSpatialSliceLink H →
        Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  ∑ target ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
        H source distinguishedTarget,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
      H N hN beta hbeta B target source
      (g₁ target) (g₂ target) (h target) (k target)

/-- The corresponding target-indexed finite-step terminal-response column. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTargetIndexedNStepTerminalRemoteColumn
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source distinguishedTarget : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₁ g₂ h k :
      PeriodicHypercubicEvenSpatialSliceLink H →
        Matrix.specialUnitaryGroup (Fin N) ℂ)
    (n : ℕ) : ℝ :=
  ∑ target ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
        H source distinguishedTarget,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioNStepTerminalResponseAbs
      H N hN beta hbeta B target source
      (g₁ target) (g₂ target) (h target) (k target) n

/-- Constant target families recover the previously formalized common-tuple
remote response column exactly. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTargetIndexedRemoteResponseColumn_const
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source distinguishedTarget : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₁ g₂ h k : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTargetIndexedRemoteResponseColumn
        H N hN beta hbeta B source distinguishedTarget
        (fun _ => g₁) (fun _ => g₂) (fun _ => h) (fun _ => k) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteResponseColumn
        H N hN beta hbeta B source distinguishedTarget g₁ g₂ h k := by
  rfl

/-- Constant target families also recover the old finite-step terminal column. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTargetIndexedNStepTerminalRemoteColumn_const
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source distinguishedTarget : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₁ g₂ h k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTargetIndexedNStepTerminalRemoteColumn
        H N hN beta hbeta B source distinguishedTarget
        (fun _ => g₁) (fun _ => g₂) (fun _ => h) (fun _ => k) n =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioNStepTerminalRemoteColumn
        H N hN beta hbeta B source distinguishedTarget g₁ g₂ h k n := by
  rfl

/-- The arbitrary finite-step residual decomposition survives target-indexed
test values unchanged: all target dependence stays inside the terminal column,
while the represented-source tagged transport is independent of those values. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTargetIndexedRemoteResponseColumn_le_nStepTransport_add_terminal
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source distinguishedTarget : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₁ g₂ h k :
      PeriodicHypercubicEvenSpatialSliceLink H →
        Matrix.specialUnitaryGroup (Fin N) ℂ)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTargetIndexedRemoteResponseColumn
        H N hN beta hbeta B source distinguishedTarget g₁ g₂ h k ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioNStepRemoteTransportColumn
          H beta hbeta source distinguishedTarget n +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTargetIndexedNStepTerminalRemoteColumn
          H N hN beta hbeta B source distinguishedTarget g₁ g₂ h k n := by
  classical
  let remote :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
      H source distinguishedTarget
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTargetIndexedRemoteResponseColumn
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTargetIndexedNStepTerminalRemoteColumn
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioNStepRemoteTransportColumn
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro target hTarget
  have hRemote :
      target ∉
        periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers
          H source distinguishedTarget := by
    simpa [
      remote,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers] using
      hTarget
  rcases
    periodicHypercubicEvenSpatialSlice_not_mem_C5ExceptionalBackgroundFibers
      H source distinguishedTarget target hRemote with
    ⟨hSourceTarget, _hTargetDistinguished, hNoShare⟩
  have hRaw :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_fixedRightTargetRatio_response_abs_le_taggedTransport_add_terminal_of_remote
      H N hN beta hbeta B (target := target) (source := source)
      (Ne.symm hSourceTarget) hNoShare
      (g₁ target) (g₂ target) (h target) (k target) n
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioNStepTerminalResponseAbs] using
    hRaw

/-- Even with independent targetwise SU(N) test values, the whole terminal
column is bounded by twice the physical-left total mass of the same aggregate
remote variation profile.  The right-hand side contains no targetwise group
values. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTargetIndexedNStepTerminalRemoteColumn_le_two_mul_remoteAggregateLeftVariationTotal
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source distinguishedTarget : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₁ g₂ h k :
      PeriodicHypercubicEvenSpatialSliceLink H →
        Matrix.specialUnitaryGroup (Fin N) ℂ)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTargetIndexedNStepTerminalRemoteColumn
        H N hN beta hbeta B source distinguishedTarget g₁ g₂ h k n ≤
      2 *
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
            H beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteAggregateVariation
              H beta source distinguishedTarget)
            n (Sum.inl e) := by
  classical
  let remote :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
      H source distinguishedTarget
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTargetIndexedNStepTerminalRemoteColumn
        H N hN beta hbeta B source distinguishedTarget g₁ g₂ h k n =
      ∑ target ∈ remote,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioNStepTerminalResponseAbs
          H N hN beta hbeta B target source
          (g₁ target) (g₂ target) (h target) (k target) n := by
            rfl
    _ ≤
      ∑ target ∈ remote,
        2 *
          ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
              H beta hbeta
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
                H beta target)
              n (Sum.inl e) := by
      apply Finset.sum_le_sum
      intro target hTarget
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioNStepTerminalResponseAbs_le_two_mul_leftVariationTotal
          H N hN beta hbeta B target source
          (g₁ target) (g₂ target) (h target) (k target) n
    _ =
      2 *
        ∑ target ∈ remote,
          ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
              H beta hbeta
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
                H beta target)
              n (Sum.inl e) := by
      rw [Finset.mul_sum]
    _ =
      2 *
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          ∑ target ∈ remote,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
              H beta hbeta
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
                H beta target)
              n (Sum.inl e) := by
      congr 1
      rw [Finset.sum_comm]
    _ =
      2 *
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
            H beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteAggregateVariation
              H beta source distinguishedTarget)
            n (Sum.inl e) := by
      congr 1
      apply Finset.sum_congr rfl
      intro e hE
      symm
      simpa [remote] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteAggregateVariation_iterate_eq_sum
          H beta hbeta source distinguishedTarget n (Sum.inl e)

/-- Target-indexed worst-case preparation: for every finite scan depth, the
entire remote response family is reduced to the same two aggregate tagged
quantities as in the common-tuple theorem.  Thus the bound is uniform over
independent targetwise choices of `g₁,g₂,h,k`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTargetIndexedRemoteResponseColumn_le_nStepAggregateRight_add_two_mul_leftVariationTotal
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source distinguishedTarget : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₁ g₂ h k :
      PeriodicHypercubicEvenSpatialSliceLink H →
        Matrix.specialUnitaryGroup (Fin N) ℂ)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTargetIndexedRemoteResponseColumn
        H N hN beta hbeta B source distinguishedTarget g₁ g₂ h k ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
          H beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteAggregateVariation
            H beta source distinguishedTarget)
          n (Sum.inr source) +
        2 *
          ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
              H beta hbeta
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteAggregateVariation
                H beta source distinguishedTarget)
              n (Sum.inl e) := by
  have hResidual :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTargetIndexedRemoteResponseColumn_le_nStepTransport_add_terminal
      H N hN beta hbeta B source distinguishedTarget g₁ g₂ h k n
  have hTerminal :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTargetIndexedNStepTerminalRemoteColumn_le_two_mul_remoteAggregateLeftVariationTotal
      H N hN beta hbeta B source distinguishedTarget g₁ g₂ h k n
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTargetIndexedRemoteResponseColumn
        H N hN beta hbeta B source distinguishedTarget g₁ g₂ h k ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioNStepRemoteTransportColumn
          H beta hbeta source distinguishedTarget n +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTargetIndexedNStepTerminalRemoteColumn
          H N hN beta hbeta B source distinguishedTarget g₁ g₂ h k n :=
      hResidual
    _ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioNStepRemoteTransportColumn
          H beta hbeta source distinguishedTarget n +
        2 *
          ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
              H beta hbeta
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteAggregateVariation
                H beta source distinguishedTarget)
              n (Sum.inl e) := by
      exact add_le_add_right hTerminal _
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
          H beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteAggregateVariation
            H beta source distinguishedTarget)
          n (Sum.inr source) +
        2 *
          ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
              H beta hbeta
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteAggregateVariation
                H beta source distinguishedTarget)
              n (Sum.inl e) := by
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioNStepRemoteTransportColumn_eq_aggregateIterate]

end

end MathlibAnalytic
end MGAP4D
