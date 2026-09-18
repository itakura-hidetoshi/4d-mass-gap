import MGAP4D.MathlibAnalytic.CubicSpatialShellGeometricSummability
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceTwoStepTerminalCovarianceSpatialBaseL1DecayBridge
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceTwoStepTerminalSpatialBaseL1PolynomialShellBound
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

local instance twoStepTerminalCubicBaseL1ShellSpatialLinkFintype
    (H : Nat) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Pure three-dimensional geometry interface for the actual terminal base-L1
radius. The bound is volume independent and uses the cubic majorant
3 * (2*r+1)^3. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalRemoteCubicSpatialBaseL1ShellGeometryBound :
    Prop :=
  forall H : Nat,
    forall source : PeriodicHypercubicEvenSpatialSliceLink H,
      forall r : Nat,
        (((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
              H source source).filter
            (fun target =>
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalSpatialBaseL1Distance
                H target source = r)).card : Real) <=
          cubicSpatialShellMajorant r

/-- The proved polynomial shell theorem realizes the cubic geometry interface. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalRemoteCubicSpatialBaseL1ShellGeometryBound_proved :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalRemoteCubicSpatialBaseL1ShellGeometryBound := by
  intro H source r
  have hNat :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalRemoteSpatialBaseL1Shell_card_le_polynomial
      H source r
  have hCast :
      (((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
            H source source).filter
          (fun target =>
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalSpatialBaseL1Distance
              H target source = r)).card : Real) <=
        (((3 * (2 * r + 1) ^ 3 : Nat) : Real)) := by
    exact_mod_cast hNat
  have hRhs :
      (((3 * (2 * r + 1) ^ 3 : Nat) : Real)) =
        cubicSpatialShellMajorant r := by
    unfold cubicSpatialShellMajorant
    push_cast
    ring
  rw [hRhs] at hCast
  exact hCast

/-- Total terminal mass associated with the cubic spatial shell profile and a
pointwise geometric terminal response bound. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCubicSpatialBaseL1ShellMass
    (C q : Real) : Real :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalSpatialShellMass
    C q cubicSpatialShellMajorant

/-- The proved cubic base-L1 geometry and pointwise geometric terminal decay
imply the uniform two-step terminal envelope whenever 0 <= q < 1.

The finite cutoff required by the generic shell theorem is generated from the
finite remote target set itself. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCubicSpatialBaseL1Shell_to_terminalRemoteUniformBound
    (N : Nat) (hN : 0 < N) (beta : Real) (hbeta : 0 <= beta)
    (terminalPrefactor terminalRatio : Real)
    (hTerminalPrefactor : 0 <= terminalPrefactor)
    (hTerminalRatio : 0 <= terminalRatio)
    (hTerminalRatioLtOne : terminalRatio < 1)
    (hDecay :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalResponseSpatialBaseL1DecayBound
        N hN beta hbeta terminalPrefactor terminalRatio) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalRemoteUniformBound
      N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCubicSpatialBaseL1ShellMass
        terminalPrefactor terminalRatio) := by
  apply
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalRemoteSpatialShellDecayBound_to_terminalRemoteUniformBound
      N hN beta hbeta
      terminalPrefactor terminalRatio cubicSpatialShellMajorant
      hTerminalPrefactor hTerminalRatio
      cubicSpatialShellMajorant_nonneg
      (summable_cubicSpatialShellMajorant_mul_geometric_of_nonneg_lt_one
        terminalPrefactor terminalRatio hTerminalRatio hTerminalRatioLtOne)
  intro H B source
  let radius : PeriodicHypercubicEvenSpatialSliceLink H -> Nat :=
    fun target =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalSpatialBaseL1Distance
        H target source
  let remote :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
      H source source
  let cutoff : Nat :=
    (∑ target in remote, radius target) + 1
  refine ⟨radius, cutoff, ?_, ?_, ?_⟩
  · intro target hTarget
    have hLe :
        radius target <= ∑ t in remote, radius t := by
      exact
        Finset.single_le_sum
          (fun t _ht => Nat.zero_le (radius t))
          (by simpa [remote] using hTarget)
    simpa [cutoff] using Nat.lt_succ_of_le hLe
  · intro r _hr
    simpa [remote, radius] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalRemoteCubicSpatialBaseL1ShellGeometryBound_proved
        H source r
  · intro target hTarget g1 g2 h k
    simpa [radius] using
      hDecay H B source target
        (by simpa [remote] using hTarget)
        g1 g2 h k

/-- The cubic spatial shell route discharges the current uniform remote
residual certificate without an artificial condition such as 18*q < 1. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCubicSpatialBaseL1Shell_to_remoteResidualUniformBound
    (N : Nat) (hN : 0 < N) (beta : Real) (hbeta : 0 <= beta)
    (terminalPrefactor terminalRatio : Real)
    (hTerminalPrefactor : 0 <= terminalPrefactor)
    (hTerminalRatio : 0 <= terminalRatio)
    (hTerminalRatioLtOne : terminalRatio < 1)
    (hDecay :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalResponseSpatialBaseL1DecayBound
        N hN beta hbeta terminalPrefactor terminalRatio) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemoteResidualUniformBound
      N hN beta hbeta
      (Real.exp (16 * beta) *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepRemoteTransportCoefficient
            beta +
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCubicSpatialBaseL1ShellMass
            terminalPrefactor terminalRatio)) := by
  apply
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalRemoteUniformBound_to_remoteResidualUniformBound
      N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCubicSpatialBaseL1ShellMass
        terminalPrefactor terminalRatio)
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCubicSpatialBaseL1Shell_to_terminalRemoteUniformBound
      N hN beta hbeta terminalPrefactor terminalRatio
      hTerminalPrefactor hTerminalRatio hTerminalRatioLtOne hDecay

/-- After the denominator floor, covariance normal form, proved cubic geometry,
and polynomial-geometric summability, the remote residual obstruction reduces
to one analytic statement: exponential base-L1 decay of the exact ground-state
kernel-section covariance. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCovarianceCubicSpatialBaseL1Shell_to_remoteResidualUniformBound
    (N : Nat) (hN : 0 < N) (beta : Real) (hbeta : 0 <= beta)
    (covariancePrefactor covarianceRatio : Real)
    (hCovariancePrefactor : 0 <= covariancePrefactor)
    (hCovarianceRatio : 0 <= covarianceRatio)
    (hCovarianceRatioLtOne : covarianceRatio < 1)
    (hCovariance :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCovarianceSpatialBaseL1DecayBound
        N hN beta hbeta covariancePrefactor covarianceRatio) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemoteResidualUniformBound
      N hN beta hbeta
      (Real.exp (16 * beta) *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepRemoteTransportCoefficient
            beta +
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCubicSpatialBaseL1ShellMass
            (Real.exp (2 * beta) * covariancePrefactor) covarianceRatio)) := by
  apply
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCubicSpatialBaseL1Shell_to_remoteResidualUniformBound
      N hN beta hbeta
      (Real.exp (2 * beta) * covariancePrefactor) covarianceRatio
      (mul_nonneg (Real.exp_nonneg _) hCovariancePrefactor)
      hCovarianceRatio hCovarianceRatioLtOne
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCovarianceSpatialBaseL1DecayBound_to_terminalResponseSpatialBaseL1DecayBound
      N hN beta hbeta covariancePrefactor covarianceRatio hCovariance

end

end MathlibAnalytic
end MGAP4D
