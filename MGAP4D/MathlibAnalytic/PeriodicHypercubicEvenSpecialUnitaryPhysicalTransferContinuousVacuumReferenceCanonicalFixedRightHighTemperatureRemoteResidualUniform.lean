import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceDecay
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceTwoStepTerminalCubicSpatialBaseL1ShellBridge
import Mathlib.Tactic

/-!
# Canonical high-temperature uniform remote residual

The concrete canonical two-step terminal covariance decay from the preceding
unit is now fed into the already-proved cubic base-L1 shell summability bridge.

For every fixed scale s > 1 and coupling beta in that same scale's original
canonical cutoff, the terminal covariance ratio is s^{-1}, hence nonnegative
and strictly below one.  The existing cubic-shell theorem then produces a
volume- and background-uniform bound on the exact physical remote residual.

This file only closes the uniform remote-residual certificate.  It does not
assert that the resulting explicit scalar is below one, and therefore does not
yet claim a strict physical sweep contraction, Poincare/coercivity, a
Hamiltonian spectral gap, or a continuum Yang-Mills construction.
-/

namespace MGAP4D.MathlibAnalytic

noncomputable section

/-- Explicit canonical residual scalar obtained by composing the concrete
terminal covariance decay with the proved cubic shell summability and the
existing two-step remote transport coefficient. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteResidualBound
    (s beta : ℝ) : ℝ :=
  Real.exp (16 * beta) *
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepRemoteTransportCoefficient
        beta +
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCubicSpatialBaseL1ShellMass
        (Real.exp (2 * beta) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovariancePrefactor
            s beta)
        s⁻¹)

/-- The canonical terminal covariance decay discharges the existing cubic-shell
remote-residual obligation without any volume or rank factor. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperature_remoteResidualUniformBound
    (N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 1 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemoteResidualUniformBound
      N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteResidualBound
        s beta) := by
  have hsPos : 0 < s := zero_lt_one.trans hs
  have hRatioNonneg : 0 ≤ s⁻¹ :=
    inv_nonneg.mpr hsPos.le
  have hRatioLtOne : s⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ hs
  have hPrefactorNonneg :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovariancePrefactor_nonneg
      s beta hbeta hcut
  have hCovariance :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTwoStepTerminalCovarianceSpatialBaseL1DecayBound
      N hN s hs beta hbeta hcut
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteResidualBound] using
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCovarianceCubicSpatialBaseL1Shell_to_remoteResidualUniformBound
      N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovariancePrefactor
        s beta)
      s⁻¹
      hPrefactorNonneg hRatioNonneg hRatioLtOne hCovariance

end

end MGAP4D.MathlibAnalytic
