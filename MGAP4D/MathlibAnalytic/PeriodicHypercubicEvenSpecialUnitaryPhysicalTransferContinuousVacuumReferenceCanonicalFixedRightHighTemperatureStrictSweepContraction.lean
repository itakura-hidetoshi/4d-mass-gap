import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceOscillationDecay
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteResidualUniform
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceUniformRemoteResidualCertificate
import Mathlib.Tactic

/-!
# Canonical high-temperature strict physical sweep contraction

The oscillation-sharpened terminal covariance estimate is inserted into the
already-proved cubic spatial-shell bridge.  The resulting explicit remote
residual scalar vanishes at beta = 0.

For every fixed exponential scale s > 1, the cubic shell mass is linear in its
terminal prefactor at the fixed ratio s⁻¹.  This gives continuity at zero of
the sharpened residual scalar, hence continuity of the uniform physical
envelope coefficient

  18 * eta(beta) + rho_osc(s,beta).

That coefficient is exactly zero at beta = 0.  Therefore a strictly positive
coupling cutoff exists, still inside the previously selected canonical
half-barrier interval, on which the coefficient is strictly below one.

The existing uniform-residual contraction theorems then give:

* strict maximum-column contraction for every finite volume and background;
* volume-independent full-sweep exponential contraction.

No Poincare/coercivity statement, Hamiltonian spectral gap, thermodynamic
limit, or continuum construction is asserted here.
-/

namespace MGAP4D.MathlibAnalytic

open Filter
open scoped BigOperators Topology

noncomputable section

/-- Sharpened canonical remote-residual scalar obtained from the genuine
localized oscillations proved in the preceding unit. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureOscillationRemoteResidualBound
    (s beta : ℝ) : ℝ :=
  Real.exp (16 * beta) *
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepRemoteTransportCoefficient
        beta +
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCubicSpatialBaseL1ShellMass
        (Real.exp (2 * beta) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceOscillationPrefactor
            s beta)
        s⁻¹)

/-- The sharpened terminal covariance decay gives the corresponding
volume- and background-uniform exact physical remote residual certificate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperature_oscillationRemoteResidualUniformBound
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
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureOscillationRemoteResidualBound
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
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureOscillationRemoteResidualBound] using
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCovarianceCubicSpatialBaseL1Shell_to_remoteResidualUniformBound
      N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceOscillationPrefactor
        s beta)
      s⁻¹
      hPrefactorNonneg hRatioNonneg hRatioLtOne hCovariance

/-- The represented-source two-step transport coefficient is nonnegative at
nonnegative coupling. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepRemoteTransportCoefficient_nonneg
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepRemoteTransportCoefficient
        beta := by
  have hExp8 : 1 ≤ Real.exp (8 * beta) :=
    Real.one_le_exp (mul_nonneg (by norm_num) hbeta)
  have hSq8 : 1 ≤ (Real.exp (8 * beta)) ^ 2 := by
    nlinarith [sq_nonneg (Real.exp (8 * beta) - 1)]
  have hFrac8 :
      0 ≤
        ((Real.exp (8 * beta)) ^ 2 - 1) /
          ((Real.exp (8 * beta)) ^ 2 + 1) :=
    div_nonneg (sub_nonneg.mpr hSq8) (by positivity)
  have hOff :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence_nonneg
      beta hbeta
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepRemoteTransportCoefficient
  exact
    mul_nonneg
      (mul_nonneg (by norm_num) hFrac8)
      (mul_nonneg hOff (Real.exp_nonneg _))

/-- The sharpened canonical remote residual scalar is nonnegative throughout
its canonical high-temperature interval. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureOscillationRemoteResidualBound_nonneg
    (s beta : ℝ)
    (hs : 1 < s)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureOscillationRemoteResidualBound
        s beta := by
  have hsPos : 0 < s := zero_lt_one.trans hs
  have hRatioNonneg : 0 ≤ s⁻¹ := inv_nonneg.mpr hsPos.le
  have hPrefactorNonneg :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceOscillationPrefactor_nonneg
      s beta hbeta hcut
  have hTerminalPrefactor :
      0 ≤
        Real.exp (2 * beta) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceOscillationPrefactor
            s beta :=
    mul_nonneg (Real.exp_nonneg _) hPrefactorNonneg
  have hShell :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCubicSpatialBaseL1ShellMass
          (Real.exp (2 * beta) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceOscillationPrefactor
              s beta)
          s⁻¹ := by
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCubicSpatialBaseL1ShellMass
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalSpatialShellMass
    apply tsum_nonneg
    intro r
    exact
      mul_nonneg
        (cubicSpatialShellMajorant_nonneg r)
        (mul_nonneg hTerminalPrefactor (pow_nonneg hRatioNonneg r))
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureOscillationRemoteResidualBound
  exact
    mul_nonneg
      (Real.exp_nonneg _)
      (add_nonneg
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepRemoteTransportCoefficient_nonneg
          beta hbeta)
        hShell)

/-- The sharpened residual scalar vanishes exactly at the decoupled point. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureOscillationRemoteResidualBound_zero
    (s : ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureOscillationRemoteResidualBound
      s 0 = 0 := by
  simp [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureOscillationRemoteResidualBound,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepRemoteTransportCoefficient,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCubicSpatialBaseL1ShellMass,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalSpatialShellMass]

/-- At fixed geometric ratio with norm below one, the cubic shell mass is
linear in its terminal prefactor. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCubicSpatialBaseL1ShellMass_eq_mul
    (C q : ℝ)
    (hq : ‖q‖ < 1) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCubicSpatialBaseL1ShellMass
        C q =
      C *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCubicSpatialBaseL1ShellMass
          1 q := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCubicSpatialBaseL1ShellMass
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalSpatialShellMass
  have hSummable :
      Summable (fun r : ℕ =>
        cubicSpatialShellMajorant r * (1 * q ^ r)) :=
    summable_cubicSpatialShellMajorant_mul_geometric 1 q hq
  calc
    (∑' r : ℕ, cubicSpatialShellMajorant r * (C * q ^ r)) =
        ∑' r : ℕ, C * (cubicSpatialShellMajorant r * (1 * q ^ r)) := by
          apply tsum_congr
          intro r
          ring
    _ = C * ∑' r : ℕ, cubicSpatialShellMajorant r * (1 * q ^ r) :=
      hSummable.tsum_mul_left C

/-- The oscillation terminal covariance prefactor is continuous at zero for
every fixed exponential scale. -/
theorem
    continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceOscillationPrefactor_zero
    (s : ℝ) :
    ContinuousAt
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceOscillationPrefactor
        s) 0 := by
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
      s
  have hQ : ContinuousAt q 0 := by
    simpa [q] using
      continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
        s
  have hQZero :
      q 0 =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier := by
    simp [q]
  have hDenNe : 1 - q 0 ≠ 0 := by
    rw [hQZero]
    norm_num [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier]
  have hInv : ContinuousAt (fun beta : ℝ => (1 - q beta)⁻¹) 0 :=
    (continuousAt_const.sub hQ).inv₀ hDenNe
  have hCross :
      ContinuousAt
        (fun beta : ℝ =>
          Real.exp (2 * beta) - Real.exp (-2 * beta)) 0 := by
    fun_prop
  have hTarget :
      ContinuousAt
        (fun beta : ℝ =>
          Real.exp (16 * beta) - Real.exp (-16 * beta)) 0 := by
    fun_prop
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceOscillationPrefactor
  change ContinuousAt
    (fun beta : ℝ =>
      2 * (1 - q beta)⁻¹ *
        (Real.exp (2 * beta) - Real.exp (-2 * beta)) *
        (Real.exp (16 * beta) - Real.exp (-16 * beta))) 0
  exact
    (((continuousAt_const.mul hInv).mul hCross).mul hTarget)

/-- The explicit represented-source transport coefficient is continuous at
zero coupling. -/
theorem
    continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepRemoteTransportCoefficient_zero :
    ContinuousAt
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepRemoteTransportCoefficient
      0 := by
  have hK8 :
      ContinuousAt (fun beta : ℝ => (Real.exp (8 * beta)) ^ 2) 0 := by
    fun_prop
  have hFrac8 :
      ContinuousAt
        (fun beta : ℝ =>
          ((Real.exp (8 * beta)) ^ 2 - 1) /
            ((Real.exp (8 * beta)) ^ 2 + 1)) 0 := by
    exact
      (hK8.sub continuousAt_const).div
        (hK8.add continuousAt_const)
        (by norm_num)
  have hK32 :
      ContinuousAt (fun beta : ℝ => (Real.exp (32 * beta)) ^ 2) 0 := by
    fun_prop
  have hFrac32 :
      ContinuousAt
        (fun beta : ℝ =>
          ((Real.exp (32 * beta)) ^ 2 - 1) /
            ((Real.exp (32 * beta)) ^ 2 + 1)) 0 := by
    exact
      (hK32.sub continuousAt_const).div
        (hK32.add continuousAt_const)
        (by norm_num)
  have hExp16 :
      ContinuousAt (fun beta : ℝ => Real.exp (16 * beta)) 0 := by
    fun_prop
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepRemoteTransportCoefficient
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
  exact
    (continuousAt_const.mul hFrac8).mul
      ((continuousAt_const.mul hFrac32).mul hExp16)

/-- For fixed s > 1, the sharpened cubic shell contribution is continuous at
zero coupling. -/
theorem
    continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureOscillationTerminalCubicShellMass_zero
    (s : ℝ)
    (hs : 1 < s) :
    ContinuousAt
      (fun beta : ℝ =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCubicSpatialBaseL1ShellMass
          (Real.exp (2 * beta) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceOscillationPrefactor
              s beta)
          s⁻¹)
      0 := by
  have hsPos : 0 < s := zero_lt_one.trans hs
  have hRatioPos : 0 < s⁻¹ := inv_pos.mpr hsPos
  have hRatioLtOne : s⁻¹ < 1 := inv_lt_one_of_one_lt₀ hs
  have hRatioNorm : ‖s⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hRatioPos]
    exact hRatioLtOne
  have hPrefactor :
      ContinuousAt
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceOscillationPrefactor
          s) 0 :=
    continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceOscillationPrefactor_zero
      s
  have hC :
      ContinuousAt
        (fun beta : ℝ =>
          Real.exp (2 * beta) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceOscillationPrefactor
              s beta)
        0 := by
    exact (by fun_prop : ContinuousAt (fun beta : ℝ => Real.exp (2 * beta)) 0).mul hPrefactor
  have hEq :
      (fun beta : ℝ =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCubicSpatialBaseL1ShellMass
          (Real.exp (2 * beta) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceOscillationPrefactor
              s beta)
          s⁻¹) =
      (fun beta : ℝ =>
        (Real.exp (2 * beta) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceOscillationPrefactor
            s beta) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCubicSpatialBaseL1ShellMass
            1 s⁻¹) := by
    funext beta
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCubicSpatialBaseL1ShellMass_eq_mul
        (Real.exp (2 * beta) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceOscillationPrefactor
            s beta)
        s⁻¹ hRatioNorm
  rw [hEq]
  exact hC.mul continuousAt_const

/-- For every fixed s > 1, the sharpened uniform remote residual bound is
continuous at zero coupling. -/
theorem
    continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureOscillationRemoteResidualBound_zero
    (s : ℝ)
    (hs : 1 < s) :
    ContinuousAt
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureOscillationRemoteResidualBound
        s) 0 := by
  have hExp16 :
      ContinuousAt (fun beta : ℝ => Real.exp (16 * beta)) 0 := by
    fun_prop
  have hTransport :=
    continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepRemoteTransportCoefficient_zero
  have hShell :=
    continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureOscillationTerminalCubicShellMass_zero
      s hs
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureOscillationRemoteResidualBound
  exact hExp16.mul (hTransport.add hShell)

/-- The resulting uniform envelope coefficient is continuous at the decoupled
point. -/
theorem
    continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureOscillationUniformEnvelopeColumnCoefficient_zero
    (s : ℝ)
    (hs : 1 < s) :
    ContinuousAt
      (fun beta : ℝ =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformEnvelopeColumnCoefficient
          beta
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureOscillationRemoteResidualBound
            s beta))
      0 := by
  have hEta :=
    continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence_zero
  have hRho :=
    continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureOscillationRemoteResidualBound_zero
      s hs
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformEnvelopeColumnCoefficient
  exact (continuousAt_const.mul hEta).add hRho

/-- The sharpened uniform envelope coefficient is exactly zero at beta = 0. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureOscillationUniformEnvelopeColumnCoefficient_zero
    (s : ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformEnvelopeColumnCoefficient
      0
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureOscillationRemoteResidualBound
        s 0) = 0 := by
  simp [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformEnvelopeColumnCoefficient]

/-- Zero-coupling continuity produces a strictly positive interval, still
inside the canonical half-barrier interval, on which the full uniform physical
envelope coefficient is strictly below one. -/
theorem
    exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictSweepCutoff
    (s : ℝ)
    (hs : 1 < s) :
    ∃ couplingCutoff : ℝ,
      0 < couplingCutoff ∧
      couplingCutoff ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s ∧
      ∀ beta : ℝ,
        0 ≤ beta →
        beta ≤ couplingCutoff →
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformEnvelopeColumnCoefficient
          beta
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureOscillationRemoteResidualBound
            s beta) < 1 := by
  let F := fun beta : ℝ =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformEnvelopeColumnCoefficient
      beta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureOscillationRemoteResidualBound
        s beta)
  have hContinuous : ContinuousAt F 0 := by
    simpa [F] using
      continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureOscillationUniformEnvelopeColumnCoefficient_zero
        s hs
  rw [Metric.continuousAt_iff] at hContinuous
  obtain ⟨delta, hDelta, hControl⟩ :=
    hContinuous 1 (by norm_num)
  let cutoff :=
    min (delta / 2)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
        s)
  have hHalfPos :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff_pos
      s
  have hCutoffPos : 0 < cutoff := by
    dsimp [cutoff]
    exact lt_min (by positivity) hHalfPos
  refine ⟨cutoff, hCutoffPos, ?_, ?_⟩
  · dsimp [cutoff]
    exact min_le_right _ _
  · intro beta hbeta hbetaCutoff
    have hBetaDeltaHalf :
        beta ≤ delta / 2 := by
      exact hbetaCutoff.trans (by
        dsimp [cutoff]
        exact min_le_left _ _)
    have hBetaDelta : beta < delta := by
      have hHalfLt : delta / 2 < delta := by linarith
      exact lt_of_le_of_lt hBetaDeltaHalf hHalfLt
    have hDistance : dist beta 0 < delta := by
      rw [Real.dist_eq]
      simpa [abs_of_nonneg hbeta] using hBetaDelta
    have hImage := hControl hDistance
    have hAbs : |F beta - F 0| < 1 := by
      simpa [Real.dist_eq] using hImage
    have hUpper : F beta - F 0 < 1 :=
      lt_of_le_of_lt (le_abs_self (F beta - F 0)) hAbs
    have hZero : F 0 = 0 := by
      simp [F]
    rw [hZero] at hUpper
    simpa [F] using hUpper

/-- Chosen canonical strict-sweep cutoff for a fixed scale s > 1. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictSweepCutoff
    (s : ℝ)
    (hs : 1 < s) : ℝ :=
  Classical.choose
    (exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictSweepCutoff
      s hs)

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictSweepCutoff_pos
    (s : ℝ)
    (hs : 1 < s) :
    0 <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictSweepCutoff
        s hs :=
  (Classical.choose_spec
    (exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictSweepCutoff
      s hs)).1

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictSweepCutoff_le_halfBarrierCutoff
    (s : ℝ)
    (hs : 1 < s) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictSweepCutoff
        s hs ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
        s :=
  (Classical.choose_spec
    (exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictSweepCutoff
      s hs)).2.1

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictSweepCutoff_spec
    (s : ℝ)
    (hs : 1 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictSweepCutoff
          s hs) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformEnvelopeColumnCoefficient
      beta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureOscillationRemoteResidualBound
        s beta) < 1 :=
  (Classical.choose_spec
    (exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictSweepCutoff
      s hs)).2.2
    beta hbeta hcut

/-- On the chosen strict-sweep interval, every finite-volume physical envelope
has maximum column strictly below one. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperaturePhysicalLeftInfluenceEnvelopeKernel_maximumColumn_lt_one
    (N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 1 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictSweepCutoff
          s hs)
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    finiteInfluenceKernelMaximumColumnSum
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
        H N hN beta hbeta A) < 1 := by
  have hHalfCut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s :=
    hcut.trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictSweepCutoff_le_halfBarrierCutoff
        s hs)
  have hUniform :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperature_oscillationRemoteResidualUniformBound
      N hN s hs beta hbeta hHalfCut
  have hGate :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictSweepCutoff_spec
      s hs beta hbeta hcut
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_maximumColumn_lt_one_of_uniformResidual
      N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureOscillationRemoteResidualBound
        s beta)
      hUniform hGate H A

/-- Volume-independent full-sweep exponential contraction in the concrete
canonical strict high-temperature regime. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperaturePhysicalLeftInfluenceEnvelopeKernel_uniformFullSweepIterate_le_exp
    (N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 1 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictSweepCutoff
          s hs)
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (bound : ℝ)
    (hBoundNonneg : 0 ≤ bound)
    (hVariationBound : ∀ e, variation e ≤ bound)
    (sweeps : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    finiteInfluenceKernelRandomScanVariationIterate
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
        H N hN beta hbeta A)
      variation
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) * sweeps)
      source ≤
    Real.exp
        (-(1 -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformEnvelopeColumnCoefficient
            beta
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureOscillationRemoteResidualBound
              s beta)) *
          (sweeps : ℝ)) *
      bound := by
  have hHalfCut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s :=
    hcut.trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictSweepCutoff_le_halfBarrierCutoff
        s hs)
  have hUniform :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperature_oscillationRemoteResidualUniformBound
      N hN s hs beta hbeta hHalfCut
  have hRho :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureOscillationRemoteResidualBound_nonneg
      s beta hs hbeta hHalfCut
  have hGate :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictSweepCutoff_spec
      s hs beta hbeta hcut
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_uniformFullSweepIterate_le_exp
      N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureOscillationRemoteResidualBound
        s beta)
      hRho hUniform hGate H A variation hVariationNonneg
      bound hBoundNonneg hVariationBound sweeps source

end

end MGAP4D.MathlibAnalytic
