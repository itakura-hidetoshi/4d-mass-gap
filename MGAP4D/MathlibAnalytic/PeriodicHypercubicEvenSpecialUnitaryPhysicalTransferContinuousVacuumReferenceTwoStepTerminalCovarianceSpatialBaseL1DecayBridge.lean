import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceTwoStepTerminalCrossingDenominatorFloor
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceTwoStepTerminalExponentialShellCertificate
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

local instance twoStepTerminalCovarianceBaseL1DecayBridgeSpecialUnitaryMeasurableSpace
    (N : Nat) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) Complex) :=
  specialUnitaryGroupMeasurableSpace N

/-- A source-aligned remote terminal target is distinct from the source. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers_mem_ne_source
    (H : Nat)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (hTarget :
      target ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
          H source source) :
    target ≠ source := by
  have hRemote :
      target ∉
        periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers
          H source source := by
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers] using
      hTarget
  rcases
    periodicHypercubicEvenSpatialSlice_not_mem_C5ExceptionalBackgroundFibers
      H source source target hRemote with
    ⟨hSourceTarget, _hTargetDistinguished, _hNoShare⟩
  exact Ne.symm hSourceTarget

/-- The remaining analytic obstruction after the explicit crossing-denominator
floor: exponential spatial base-L1 decay of the exact kernel-section covariance
appearing in the two-step terminal normal form.

This statement does not identify the kernel-section law with an ordinary Gibbs
law and does not assert that such a bound has already been proved. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCovarianceSpatialBaseL1DecayBound
    (N : Nat) (hN : 0 < N) (beta : Real) (hbeta : 0 <= beta)
    (C q : Real) : Prop :=
  forall H : Nat,
    forall B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
      forall source target : PeriodicHypercubicEvenSpatialSliceLink H,
        target ∈
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
              H source source ->
          forall g1 g2 h k : Matrix.specialUnitaryGroup (Fin N) Complex,
            |realIntegralCovariance
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
                  H N hN beta hbeta
                  (Function.update (Function.update B source k) target g2))
                (fun A =>
                  specialUnitaryWilsonRelativeKernel N beta (A source) h /
                    specialUnitaryWilsonRelativeKernel N beta (A source) k)
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalObservable
                  H N hN beta hbeta B target source g1 g2 k)| <=
              C *
                q ^
                  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalSpatialBaseL1Distance
                    H target source

/-- Exponential decay of the exact kernel-section covariance implies the
pointwise terminal-response base-L1 decay bound, with only the explicit
multiplicative denominator cost exp(2 beta). -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCovarianceSpatialBaseL1DecayBound_to_terminalResponseSpatialBaseL1DecayBound
    (N : Nat) (hN : 0 < N) (beta : Real) (hbeta : 0 <= beta)
    (C q : Real)
    (hCovariance :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCovarianceSpatialBaseL1DecayBound
        N hN beta hbeta C q) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalResponseSpatialBaseL1DecayBound
      N hN beta hbeta (Real.exp (2 * beta) * C) q := by
  intro H B source target hTarget g1 g2 h k
  have hne : target ≠ source :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers_mem_ne_source
      H source target hTarget
  have hResponse :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalResponseAbs_le_exp_two_mul_abs_covariance
      H N hN beta hbeta B hne g1 g2 h k
  have hCovarianceBound :=
    hCovariance H B source target hTarget g1 g2 h k
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalResponseAbs
        H N hN beta hbeta B target source g1 g2 h k <=
      Real.exp (2 * beta) *
        |realIntegralCovariance
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
              H N hN beta hbeta
              (Function.update (Function.update B source k) target g2))
            (fun A =>
              specialUnitaryWilsonRelativeKernel N beta (A source) h /
                specialUnitaryWilsonRelativeKernel N beta (A source) k)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalObservable
              H N hN beta hbeta B target source g1 g2 k)| :=
        hResponse
    _ <=
      Real.exp (2 * beta) *
        (C *
          q ^
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalSpatialBaseL1Distance
              H target source) :=
        mul_le_mul_of_nonneg_left hCovarianceBound (Real.exp_nonneg _)
    _ =
      (Real.exp (2 * beta) * C) *
        q ^
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalSpatialBaseL1Distance
            H target source := by ring

end

end MathlibAnalytic
end MGAP4D
