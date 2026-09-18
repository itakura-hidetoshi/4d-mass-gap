import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceUniformRemoteResidualCertificate
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceTargetWorstCaseCrossRatioInfluenceMajorant
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFixedRightTargetRatioTwoStepRemoteResidualColumn
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance twoStepTerminalResidualCertificateSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance twoStepTerminalResidualCertificateSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance twoStepTerminalResidualCertificateSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance twoStepTerminalResidualCertificateSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance twoStepTerminalResidualCertificateSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance twoStepTerminalResidualCertificateSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance twoStepTerminalResidualCertificateSpatialLinkNonempty
    (H : ℕ) : Nonempty (PeriodicHypercubicEvenSpatialSliceLink H) :=
  ⟨(⟨(0 : PeriodicHypercubicEvenVertex H), by
      simp [periodicHypercubicEvenOnPrimaryReflectionPlane]⟩,
    ⟨(1 : PeriodicHypercubicAxis), by norm_num⟩)⟩

/-- The explicit volume-independent two-step represented-source transport
coefficient. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepRemoteTransportCoefficient
    (beta : ℝ) : ℝ :=
  2 * (((Real.exp (8 * beta)) ^ 2 - 1) /
      ((Real.exp (8 * beta)) ^ 2 + 1)) *
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
      beta * Real.exp (16 * beta))

/-- A uniform terminal certificate after two restricted random-scan steps.

For every finite volume, background and physical source, one supplies a
nonnegative target envelope which dominates every SU(N) four-tuple terminal
response on the source-aligned remote target set, with total remote mass at
most tau.  The certificate makes no supremum-attainment assumption. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalRemoteUniformBound
    (N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (tau : ℝ) : Prop :=
  ∀ H : ℕ,
    ∀ B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
      ∀ source : PeriodicHypercubicEvenSpatialSliceLink H,
        ∃ terminal : PeriodicHypercubicEvenSpatialSliceLink H → ℝ,
          (∀ target,
            target ∈
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
                  H source source →
              0 ≤ terminal target) ∧
          (∀ target,
            target ∈
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
                  H source source →
              ∀ g₁ g₂ h k : Matrix.specialUnitaryGroup (Fin N) ℂ,
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalResponseAbs
                    H N hN beta hbeta B target source g₁ g₂ h k ≤
                  terminal target) ∧
          (∑ target ∈
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
                H source source,
            terminal target) ≤ tau

/-- At one remote target, a tuple-uniform two-step terminal envelope controls
the targetwise worst-case cross-ratio majorant by the exact two-step transport
plus that terminal envelope.  The targetwise sSup is bounded directly; no
maximizer is chosen. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWorstCaseCrossRatioInfluenceMajorant_le_exp_sixteen_mul_twoStepTransport_add_terminal
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hne : target ≠ source)
    (hNoShare : ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source)
    (terminal : ℝ)
    (hTerminal :
      ∀ g₁ g₂ h k : Matrix.specialUnitaryGroup (Fin N) ℂ,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalResponseAbs
            H N hN beta hbeta B target source g₁ g₂ h k ≤ terminal) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant
        H N hN beta hbeta B target source ≤
      Real.exp (16 * beta) *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
            H beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
              H beta target)
            2 (Sum.inr source) +
          terminal) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant
  apply csSup_le
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioCrossRatioInfluenceMajorantSet_nonempty
      H N hN beta hbeta B target source)
  intro x hx
  rcases hx with ⟨g₁, g₂, h, k, rfl⟩
  let R : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
      H N hN beta hbeta B target source g₁ g₂ h k
  have hRNonneg : 0 ≤ R := by
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs_nonneg
        H N hN beta hbeta B target source g₁ g₂ h k
  have hLinear :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioCrossRatioInfluenceMajorant
          H N hN beta hbeta B target source g₁ g₂ h k ≤
        Real.exp (16 * beta) * R := by
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioCrossRatioInfluenceMajorant,
      R] using
      finitePositiveWeightCrossRatioInfluenceTransform_log_one_add_le
        (Real.exp (16 * beta) * R)
        (mul_nonneg (Real.exp_pos _).le hRNonneg)
  have hRaw :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_fixedRightTargetRatio_response_abs_le_taggedTransport_add_terminal_of_remote
      H N hN beta hbeta B (target := target) (source := source)
      hne hNoShare g₁ g₂ h k 2
  have hResponse :
      R ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
            H beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
              H beta target)
            2 (Sum.inr source) +
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalResponseAbs
            H N hN beta hbeta B target source g₁ g₂ h k := by
    simpa [
      R,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalResponseAbs] using
      hRaw
  have hResponseBound :
      R ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
            H beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
              H beta target)
            2 (Sum.inr source) +
          terminal := by
    exact hResponse.trans (add_le_add_right (hTerminal g₁ g₂ h k) _)
  exact hLinear.trans
    (mul_le_mul_of_nonneg_left hResponseBound (Real.exp_pos _).le)

/-- A remote terminal envelope with total mass tau bounds the complete
targetwise worst-case remote cross-ratio column by the explicit two-step
volume-independent transport coefficient plus tau. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWorstCaseRemoteCrossRatioInfluenceColumn_le_exp_sixteen_mul_twoStepTransportCoefficient_add_terminal
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (terminal : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hTerminal :
      ∀ target,
        target ∈
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
              H source source →
          ∀ g₁ g₂ h k : Matrix.specialUnitaryGroup (Fin N) ℂ,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalResponseAbs
                H N hN beta hbeta B target source g₁ g₂ h k ≤ terminal target)
    (tau : ℝ)
    (hTerminalSum :
      (∑ target ∈
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
            H source source,
        terminal target) ≤ tau) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseRemoteCrossRatioInfluenceColumn
        H N hN beta hbeta B source source ≤
      Real.exp (16 * beta) *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepRemoteTransportCoefficient
            beta +
          tau) := by
  classical
  let remote :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
      H source source
  let transport := fun target : PeriodicHypercubicEvenSpatialSliceLink H =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
      H beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
        H beta target)
      2 (Sum.inr source)
  have hGeometry :
      ∀ target ∈ remote,
        target ≠ source ∧
          ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source := by
    intro target hTarget
    have hRemote :
        target ∉ periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers
          H source source := by
      simpa [
        remote,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers] using
        hTarget
    rcases
      periodicHypercubicEvenSpatialSlice_not_mem_C5ExceptionalBackgroundFibers
        H source source target hRemote with
      ⟨hSourceTarget, _hTargetDistinguished, hNoShare⟩
    exact ⟨Ne.symm hSourceTarget, hNoShare⟩
  have hPoint :
      ∀ target ∈ remote,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant
            H N hN beta hbeta B target source ≤
          Real.exp (16 * beta) * (transport target + terminal target) := by
    intro target hTarget
    rcases hGeometry target hTarget with ⟨hne, hNoShare⟩
    simpa [transport] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWorstCaseCrossRatioInfluenceMajorant_le_exp_sixteen_mul_twoStepTransport_add_terminal
        H N hN beta hbeta B hne hNoShare (terminal target)
        (hTerminal target (by simpa [remote] using hTarget))
  have hRemoteSubset : remote ⊆ Finset.univ.erase source := by
    intro target hTarget
    have hne : target ≠ source := (hGeometry target hTarget).1
    exact Finset.mem_erase.mpr ⟨hne, Finset.mem_univ target⟩
  have hTransportSumLe :
      (∑ target ∈ remote, transport target) ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_twoStep_remoteRightColumnSum
          H beta hbeta source := by
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_twoStep_remoteRightColumnSum
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact hRemoteSubset
    · intro target _ _
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate_nonneg
          H beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
            H beta target)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_nonneg
            H beta target)
          2 (Sum.inr source)
  have hTransportUniform :
      (∑ target ∈ remote, transport target) ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepRemoteTransportCoefficient
          beta := by
    exact hTransportSumLe.trans (by
      simpa [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepRemoteTransportCoefficient] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_twoStep_remoteRightColumnSum_le
          H beta hbeta source)
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseRemoteCrossRatioInfluenceColumn
  calc
    (∑ target ∈ remote,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant
        H N hN beta hbeta B target source) ≤
      ∑ target ∈ remote,
        Real.exp (16 * beta) * (transport target + terminal target) := by
          apply Finset.sum_le_sum
          intro target hTarget
          exact hPoint target hTarget
    _ =
      Real.exp (16 * beta) *
        ((∑ target ∈ remote, transport target) +
          (∑ target ∈ remote, terminal target)) := by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib]
          rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤
      Real.exp (16 * beta) *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepRemoteTransportCoefficient
            beta +
          tau) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          exact add_le_add hTransportUniform (by simpa [remote] using hTerminalSum)

/-- A uniform two-step terminal certificate produces an explicit
volume-independent remote residual certificate.  Thus the remaining remote
obstruction is reduced to controlling only the two-step terminal envelope. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalRemoteUniformBound_to_remoteResidualUniformBound
    (N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (tau : ℝ)
    (hTerminal :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalRemoteUniformBound
        N hN beta hbeta tau) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemoteResidualUniformBound
      N hN beta hbeta
      (Real.exp (16 * beta) *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepRemoteTransportCoefficient
            beta +
          tau)) := by
  intro H B
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemoteResidualMaximumColumn
  apply finiteInfluenceKernelMaximumColumnSum_le_of_forall
  intro source
  rcases hTerminal H B source with
    ⟨terminal, _hTerminalNonneg, hTerminalPoint, hTerminalSum⟩
  have hWorst :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWorstCaseRemoteCrossRatioInfluenceColumn_le_exp_sixteen_mul_twoStepTransportCoefficient_add_terminal
      H N hN beta hbeta B source terminal hTerminalPoint tau hTerminalSum
  have hResidualEq :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual_columnSum_eq_worstCaseRemoteColumn
      H N hN beta hbeta B source
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemoteResidualKernel,
    finiteInfluenceKernelColumnSum] using
    hResidualEq.le.trans hWorst

end

end MathlibAnalytic
end MGAP4D
