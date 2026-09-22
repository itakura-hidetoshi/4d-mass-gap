import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceOscillationDecay
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceTwoStepTerminalCubicSpatialBaseL1ShellBridge
import Mathlib.Tactic

/-!
# Canonical high-temperature remote residual with vanishing oscillations

The sharpened terminal covariance estimate from the oscillation route is fed
into the already-proved cubic base-L1 shell bridge.

This produces a second, additive canonical remote-residual certificate.  It
uses the same cutoff and the same spatial decay ratio `s⁻¹` as the earlier
coarse certificate, but its terminal covariance prefactor vanishes at
`beta = 0`.

Consequently the complete explicit residual scalar also vanishes at zero
coupling.  This is the analytic normalization needed for the next strict
uniform physical sweep gate.  No previously merged definition or theorem is
modified here.
-/

namespace MGAP4D.MathlibAnalytic

noncomputable section

/-- Canonical remote-residual scalar obtained from the sharpened oscillation
terminal covariance certificate. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteResidualOscillationBound
    (s beta : ℝ) : ℝ :=
  Real.exp (16 * beta) *
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepRemoteTransportCoefficient
        beta +
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCubicSpatialBaseL1ShellMass
        (Real.exp (2 * beta) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceOscillationPrefactor
            s beta)
        s⁻¹)

/-- The sharpened canonical remote residual vanishes exactly at the decoupled
endpoint. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteResidualOscillationBound_zero
    (s : ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteResidualOscillationBound
      s 0 = 0 := by
  simp [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteResidualOscillationBound,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepRemoteTransportCoefficient,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCubicSpatialBaseL1ShellMass,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalSpatialShellMass]

/-- The sharpened covariance decay discharges the existing cubic-shell
remote-residual obligation, with no volume or rank factor. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperature_remoteResidualOscillationUniformBound
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
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteResidualOscillationBound
        s beta) := by
  have hsPos : 0 < s := zero_lt_one.trans hs
  have hRatioNonneg : 0 ≤ s⁻¹ :=
    inv_nonneg.mpr hsPos.le
  have hRatioLtOne : s⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ hs
  have hPrefactorNonneg :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceOscillationPrefactor_nonneg
      s beta hbeta hcut
  have hCovariance :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTwoStepTerminalCovarianceSpatialBaseL1OscillationDecayBound
      N hN s hs beta hbeta hcut
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteResidualOscillationBound] using
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCovarianceCubicSpatialBaseL1Shell_to_remoteResidualUniformBound
      N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceOscillationPrefactor
        s beta)
      s⁻¹
      hPrefactorNonneg hRatioNonneg hRatioLtOne hCovariance

/-- The sharpened explicit remote-residual scalar is nonnegative throughout
the same canonical high-temperature interval. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteResidualOscillationBound_nonneg
    (s beta : ℝ)
    (hs : 1 < s)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteResidualOscillationBound
        s beta := by
  have hsPos : 0 < s := zero_lt_one.trans hs
  have hRatioNonneg : 0 ≤ s⁻¹ :=
    inv_nonneg.mpr hsPos.le
  have hPrefactorNonneg :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceOscillationPrefactor_nonneg
      s beta hbeta hcut
  have hTerminalCoefficientNonneg :
      0 ≤
        Real.exp (2 * beta) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceOscillationPrefactor
            s beta :=
    mul_nonneg (Real.exp_nonneg _) hPrefactorNonneg
  have hShellNonneg :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCubicSpatialBaseL1ShellMass
          (Real.exp (2 * beta) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceOscillationPrefactor
              s beta)
          s⁻¹ := by
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCubicSpatialBaseL1ShellMass
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalSpatialShellMass
    exact tsum_nonneg (fun r =>
      mul_nonneg
        (cubicSpatialShellMajorant_nonneg r)
        (mul_nonneg hTerminalCoefficientNonneg
          (pow_nonneg hRatioNonneg r)))
  have hExpEight : 1 ≤ Real.exp (8 * beta) := by
    exact Real.one_le_exp (mul_nonneg (by norm_num) hbeta)
  have hExpEightSq : 1 ≤ (Real.exp (8 * beta)) ^ 2 := by
    nlinarith [sq_nonneg (Real.exp (8 * beta) - 1)]
  have hBoundaryRatioNonneg :
      0 ≤
        (((Real.exp (8 * beta)) ^ 2 - 1) /
          ((Real.exp (8 * beta)) ^ 2 + 1)) :=
    div_nonneg
      (sub_nonneg.mpr hExpEightSq)
      (by positivity)
  have hTransportNonneg :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepRemoteTransportCoefficient
          beta := by
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepRemoteTransportCoefficient
    exact
      mul_nonneg
        (mul_nonneg (by norm_num) hBoundaryRatioNonneg)
        (mul_nonneg
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence_nonneg
            beta hbeta)
          (Real.exp_nonneg _))
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteResidualOscillationBound
  exact
    mul_nonneg
      (Real.exp_nonneg _)
      (add_nonneg hTransportNonneg hShellNonneg)

/-- At zero coupling the uniform envelope coefficient built from the sharpened
remote residual also vanishes. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformEnvelopeColumnCoefficient_remoteResidualOscillation_zero
    (s : ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformEnvelopeColumnCoefficient
      0
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteResidualOscillationBound
        s 0) = 0 := by
  simp [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformEnvelopeColumnCoefficient]

end

end MGAP4D.MathlibAnalytic
