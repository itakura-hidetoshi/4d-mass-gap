import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFixedRightTargetRatioTwoStepRemoteColumn
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceC5ExceptionalSupport
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance fixedRightTargetRatioTwoStepRemoteResidualColumnSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance fixedRightTargetRatioTwoStepRemoteResidualColumnSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance fixedRightTargetRatioTwoStepRemoteResidualColumnSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance fixedRightTargetRatioTwoStepRemoteResidualColumnSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance fixedRightTargetRatioTwoStepRemoteResidualColumnSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance fixedRightTargetRatioTwoStepRemoteResidualColumnSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The geometrically remote target set for a fixed physical source and a
fixed distinguished right target: all spatial links outside the already
formalized C5 exceptional set. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
    (H : ℕ)
    (source distinguishedTarget : PeriodicHypercubicEvenSpatialSliceLink H) :
    Finset (PeriodicHypercubicEvenSpatialSliceLink H) := by
  classical
  exact Finset.univ \
    periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers
      H source distinguishedTarget

/-- Absolute fixed-right target-ratio response for one target/source pair. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₁ g₂ h k : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  |(∫ A,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta A B target g₁ /
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta A B target g₂
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source h) target g₂)) -
    (∫ A,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta A B target g₁ /
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta A B target g₂
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source k) target g₂))|

/-- The exact `n = 2` terminal response appearing in the stationary finite-step
response theorem, after smoothing the target-ratio observable by the common
`k`-boundary restricted random scan. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalResponseAbs
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₁ g₂ h k : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  |(∫ A,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
        H N hN beta hbeta B target source g₂ k
        (fun C =>
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                H N beta C B target g₁ /
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                H N beta C B target g₂)
        2 A
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
        2 A
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source k) target g₂))|

/-- Remote fixed-right response column outside the C5 exceptional set. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteResponseColumn
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source distinguishedTarget : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₁ g₂ h k : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  ∑ target ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
        H source distinguishedTarget,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
      H N hN beta hbeta B target source g₁ g₂ h k

/-- Remote `n = 2` terminal-response column outside the same C5 exceptional
set. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalRemoteColumn
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source distinguishedTarget : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₁ g₂ h k : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  ∑ target ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
        H source distinguishedTarget,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalResponseAbs
      H N hN beta hbeta B target source g₁ g₂ h k

/-- After two actual restricted random-scan steps, the whole geometrically
remote fixed-right response column is bounded by an explicit volume-independent
transport coefficient plus exactly one remaining terminal-response column.

This theorem performs no estimate on that terminal column.  Its role is to
isolate the remaining nonlocal obstruction after the transport term has already
been closed uniformly in volume. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteResponseColumn_le_twoStepTransport_add_terminal
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source distinguishedTarget : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₁ g₂ h k : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteResponseColumn
        H N hN beta hbeta B source distinguishedTarget g₁ g₂ h k ≤
      2 * (((Real.exp (8 * beta)) ^ 2 - 1) /
        ((Real.exp (8 * beta)) ^ 2 + 1)) *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
          beta * Real.exp (16 * beta)) +
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalRemoteColumn
        H N hN beta hbeta B source distinguishedTarget g₁ g₂ h k := by
  rfl

end

end MathlibAnalytic
end MGAP4D
