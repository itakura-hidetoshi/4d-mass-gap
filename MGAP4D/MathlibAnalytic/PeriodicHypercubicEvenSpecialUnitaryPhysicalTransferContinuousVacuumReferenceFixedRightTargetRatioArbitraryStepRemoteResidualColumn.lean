import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFixedRightTargetRatioTwoStepRemoteResidualColumn
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance fixedRightTargetRatioArbitraryStepRemoteResidualColumnSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance fixedRightTargetRatioArbitraryStepRemoteResidualColumnSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance fixedRightTargetRatioArbitraryStepRemoteResidualColumnSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance fixedRightTargetRatioArbitraryStepRemoteResidualColumnSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance fixedRightTargetRatioArbitraryStepRemoteResidualColumnSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance fixedRightTargetRatioArbitraryStepRemoteResidualColumnSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The exact `n`-step terminal response appearing in the stationary finite-step
response theorem, after smoothing the target-ratio observable by the common
`k`-boundary restricted random scan. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioNStepTerminalResponseAbs
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₁ g₂ h k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (n : ℕ) : ℝ :=
  |(∫ A,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
        H N hN beta hbeta B target source g₂ k
        (fun C =>
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                H N beta C B target g₁ /
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                H N beta C B target g₂)
        n A
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source h) target g₂)) -
    (∫ A,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
        H N hN beta hbeta B target source g₂ k
        (fun C =>
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                H N beta C B target g₁ /
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                H N beta C B target g₂)
        n A
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source k) target g₂))|

/-- The geometrically remote represented-source transport column after `n`
actual restricted random-scan steps. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioNStepRemoteTransportColumn
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source distinguishedTarget : PeriodicHypercubicEvenSpatialSliceLink H)
    (n : ℕ) : ℝ :=
  ∑ target ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
        H source distinguishedTarget,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
      H beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
        H beta target)
      n (Sum.inr source)

/-- The geometrically remote `n`-step terminal-response column. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioNStepTerminalRemoteColumn
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source distinguishedTarget : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₁ g₂ h k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (n : ℕ) : ℝ :=
  ∑ target ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
        H source distinguishedTarget,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioNStepTerminalResponseAbs
      H N hN beta hbeta B target source g₁ g₂ h k n

/-- At every finite step `n`, the whole geometrically remote fixed-right
response column is bounded by the represented-source transport accumulated by
that step plus exactly the corresponding terminal-response column.

This is the finite-step form needed to separate the two remaining analytic
obligations: a uniform bound on the represented-source transport column and
vanishing of the terminal remote column along finite powers.  Neither obligation
is asserted here. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteResponseColumn_le_nStepTransport_add_terminal
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source distinguishedTarget : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₁ g₂ h k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteResponseColumn
        H N hN beta hbeta B source distinguishedTarget g₁ g₂ h k ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioNStepRemoteTransportColumn
          H beta hbeta source distinguishedTarget n +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioNStepTerminalRemoteColumn
          H N hN beta hbeta B source distinguishedTarget g₁ g₂ h k n := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteResponseColumn
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioNStepRemoteTransportColumn
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioNStepTerminalRemoteColumn
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro target hTarget
  have hRemote :
      target ∉
        periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers
          H source distinguishedTarget := by
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers] using
      hTarget
  rcases
    periodicHypercubicEvenSpatialSlice_not_mem_C5ExceptionalBackgroundFibers
      H source distinguishedTarget target hRemote with
    ⟨hSourceTarget, _hTargetDistinguished, hNoShare⟩
  have hRaw :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_fixedRightTargetRatio_response_abs_le_taggedTransport_add_terminal_of_remote
      H N hN beta hbeta B (target := target) (source := source)
      (Ne.symm hSourceTarget) hNoShare g₁ g₂ h k n
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioNStepTerminalResponseAbs] using
    hRaw

end

end MathlibAnalytic
end MGAP4D
