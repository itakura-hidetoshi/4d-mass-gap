import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteResidualOscillationUniform
import Mathlib.Tactic

/-!
# Canonical strict physical sweep gate from vanishing oscillations

The oscillation-sharpened canonical remote residual now vanishes at
`beta = 0`.  This file turns that normalization into a strict physical sweep
gate on a strictly positive, volume-independent coupling interval.

The only infinite shell appearing in the residual is first factored into

  amplitude(beta) * shellMass(1, s⁻¹).

Thus the beta dependence is finite-dimensional.  The terminal oscillation
prefactor, the two-step transport coefficient, the sharpened remote residual
and finally the uniform envelope coefficient are continuous at zero.  Since

  c_env(0, rho_osc(s,0)) = 0,

ordinary epsilon-delta continuity yields a positive cutoff below the already
proved canonical half-barrier cutoff on which `c_env < 1`.

The existing uniform-residual contraction theorems then give strict
maximum-column contraction and volume-independent full-sweep exponential
contraction for every finite volume and every background.
-/

namespace MGAP4D.MathlibAnalytic

open Filter
open scoped BigOperators Topology

noncomputable section

local instance canonicalStrictPhysicalSweepGateSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance canonicalStrictPhysicalSweepGateSpatialLinkNonempty
    (H : ℕ) : Nonempty (PeriodicHypercubicEvenSpatialSliceLink H) :=
  ⟨(⟨(0 : PeriodicHypercubicEvenVertex H), by
      simp [periodicHypercubicEvenOnPrimaryReflectionPlane]⟩,
    ⟨(1 : PeriodicHypercubicAxis), by norm_num⟩)⟩

/-- The cubic shell mass is exactly linear in its pointwise covariance
amplitude.  The geometric ratio is kept fixed. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCubicSpatialBaseL1ShellMass_eq_mul_unit
    (C q : ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCubicSpatialBaseL1ShellMass
        C q =
      C *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCubicSpatialBaseL1ShellMass
          1 q := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCubicSpatialBaseL1ShellMass
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalSpatialShellMass
  calc
    (∑' r : ℕ,
      cubicSpatialShellMajorant r * (C * q ^ r)) =
        ∑' r : ℕ,
          C * (cubicSpatialShellMajorant r * q ^ r) := by
            apply tsum_congr
            intro r
            ring
    _ = C * ∑' r : ℕ, cubicSpatialShellMajorant r * q ^ r := by
      rw [tsum_mul_left]
    _ = C *
        ∑' r : ℕ, cubicSpatialShellMajorant r * (1 * q ^ r) := by
      simp

/-- The sharpened terminal covariance prefactor is continuous at the
decoupled endpoint. -/
theorem
    continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceOscillationPrefactor
    (s : ℝ) :
    ContinuousAt
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceOscillationPrefactor
        s)
      0 := by
  have hQ :
      ContinuousAt
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
          s)
        0 :=
    continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
      s
  have hGap :
      ContinuousAt
        (fun beta : ℝ =>
          1 -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
              s beta)
        0 :=
    continuousAt_const.sub hQ
  have hGapZero :
      1 -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
          s 0 ≠ 0 := by
    simp [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier]
  have hInv :
      ContinuousAt
        (fun beta : ℝ =>
          (1 -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
              s beta)⁻¹)
        0 :=
    hGap.fun_inv₀ hGapZero
  have hOscTwo :
      ContinuousAt
        (fun beta : ℝ =>
          Real.exp (2 * beta) - Real.exp (-2 * beta))
        0 := by
    fun_prop
  have hOscSixteen :
      ContinuousAt
        (fun beta : ℝ =>
          Real.exp (16 * beta) - Real.exp (-16 * beta))
        0 := by
    fun_prop
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceOscillationPrefactor
  exact
    (((continuousAt_const.mul hInv).mul hOscTwo).mul hOscSixteen)

/-- The explicit two-step represented-source transport coefficient is
continuous at zero coupling. -/
theorem
    continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepRemoteTransportCoefficient_zero :
    ContinuousAt
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepRemoteTransportCoefficient
      0 := by
  have hK :
      Continuous
        (fun beta : ℝ => (Real.exp (8 * beta)) ^ 2) := by
    fun_prop
  have hRatio :
      ContinuousAt
        (fun beta : ℝ =>
          (((Real.exp (8 * beta)) ^ 2 - 1) /
            ((Real.exp (8 * beta)) ^ 2 + 1)))
        0 := by
    exact
      ((hK.sub continuous_const).div
        (hK.add continuous_const)
        (fun beta => by
          have hsq : 0 < (Real.exp (8 * beta)) ^ 2 :=
            pow_pos (Real.exp_pos _) 2
          linarith)).continuousAt
  have hOff :
      ContinuousAt
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
        0 := by
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence] using
      continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence_zero
  have hExp :
      ContinuousAt (fun beta : ℝ => Real.exp (16 * beta)) 0 := by
    fun_prop
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepRemoteTransportCoefficient
  exact
    (continuousAt_const.mul hRatio).mul (hOff.mul hExp)

/-- The oscillation-sharpened remote residual is continuous at zero.  The
infinite cubic shell causes no new beta-continuity problem because its
amplitude factors out exactly. -/
theorem
    continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteResidualOscillationBound
    (s : ℝ) :
    ContinuousAt
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteResidualOscillationBound
        s)
      0 := by
  let P : ℝ → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceOscillationPrefactor
      s
  let A : ℝ → ℝ :=
    fun beta =>
      Real.exp (2 * beta) * P beta
  let K : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCubicSpatialBaseL1ShellMass
      1 s⁻¹
  have hP : ContinuousAt P 0 := by
    simpa [P] using
      continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceOscillationPrefactor
        s
  have hExpTwo :
      ContinuousAt (fun beta : ℝ => Real.exp (2 * beta)) 0 := by
    fun_prop
  have hA : ContinuousAt A 0 := by
    simpa [A] using hExpTwo.mul hP
  have hShell :
      ContinuousAt
        (fun beta : ℝ =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCubicSpatialBaseL1ShellMass
            (A beta) s⁻¹)
        0 := by
    have hEq :
        (fun beta : ℝ =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCubicSpatialBaseL1ShellMass
            (A beta) s⁻¹) =
          fun beta => A beta * K := by
      funext beta
      simpa [K] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCubicSpatialBaseL1ShellMass_eq_mul_unit
          (A beta) s⁻¹
    rw [hEq]
    exact hA.mul continuousAt_const
  have hTransport :
      ContinuousAt
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepRemoteTransportCoefficient
        0 :=
    continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepRemoteTransportCoefficient_zero
  have hExpSixteen :
      ContinuousAt (fun beta : ℝ => Real.exp (16 * beta)) 0 := by
    fun_prop
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteResidualOscillationBound
  change
    ContinuousAt
      (fun beta : ℝ =>
        Real.exp (16 * beta) *
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepRemoteTransportCoefficient
              beta +
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCubicSpatialBaseL1ShellMass
              (A beta) s⁻¹))
      0
  exact hExpSixteen.mul (hTransport.add hShell)

/-- The full uniform physical envelope coefficient built from the sharpened
remote residual is continuous at zero. -/
theorem
    continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformEnvelopeColumnCoefficient_remoteResidualOscillation
    (s : ℝ) :
    ContinuousAt
      (fun beta : ℝ =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformEnvelopeColumnCoefficient
          beta
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteResidualOscillationBound
            s beta))
      0 := by
  have hEta :
      ContinuousAt
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
        0 :=
    continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence_zero
  have hRho :
      ContinuousAt
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteResidualOscillationBound
          s)
        0 :=
    continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteResidualOscillationBound
      s
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformEnvelopeColumnCoefficient
  exact
    (continuousAt_const.mul hEta).add hRho

/-- Zero-coupling continuity yields a strictly positive interval, contained in
the existing canonical half-barrier interval, on which the complete physical
uniform envelope coefficient is strictly below one. -/
theorem
    exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
    (s : ℝ) :
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
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteResidualOscillationBound
                s beta) < 1 := by
  let C : ℝ → ℝ :=
    fun beta =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformEnvelopeColumnCoefficient
        beta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteResidualOscillationBound
          s beta)
  have hContinuous : ContinuousAt C 0 := by
    simpa [C] using
      continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformEnvelopeColumnCoefficient_remoteResidualOscillation
        s
  rw [Metric.continuousAt_iff] at hContinuous
  obtain ⟨delta, hDelta, hControl⟩ :=
    hContinuous 1 (by norm_num)
  let baseCutoff :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
      s
  let couplingCutoff := min (delta / 2) baseCutoff
  have hBaseCutoff : 0 < baseCutoff := by
    simpa [baseCutoff] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff_pos
        s
  have hHalfDelta : 0 < delta / 2 := by positivity
  have hCutoffPos : 0 < couplingCutoff := by
    dsimp [couplingCutoff]
    exact lt_min hHalfDelta hBaseCutoff
  refine ⟨couplingCutoff, hCutoffPos, ?_, ?_⟩
  · dsimp [couplingCutoff]
    exact min_le_right _ _
  · intro beta hBeta hBetaCutoff
    have hBetaHalfDelta :
        beta ≤ delta / 2 :=
      hBetaCutoff.trans (by
        dsimp [couplingCutoff]
        exact min_le_left _ _)
    have hBetaDelta : beta < delta := by
      linarith
    have hDistance : dist beta 0 < delta := by
      rw [Real.dist_eq]
      simp [abs_of_nonneg hBeta]
      exact hBetaDelta
    have hImage := hControl hDistance
    have hAbs : |C beta - C 0| < 1 := by
      simpa [Real.dist_eq] using hImage
    have hUpper : C beta - C 0 < 1 :=
      lt_of_le_of_lt (le_abs_self (C beta - C 0)) hAbs
    have hZero : C 0 = 0 := by
      simp [C]
    rw [hZero] at hUpper
    simpa [C] using hUpper

/-- Canonical strictly positive cutoff for the complete physical sweep gate. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
    (s : ℝ) : ℝ :=
  Classical.choose
    (exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
      s)

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff_pos
    (s : ℝ) :
    0 <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
        s :=
  (Classical.choose_spec
    (exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
      s)).1

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff_le_halfBarrierCutoff
    (s : ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
        s ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
        s :=
  (Classical.choose_spec
    (exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
      s)).2.1

/-- Strict complete uniform-envelope gate on the selected canonical interval. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff_spec
    (s beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformEnvelopeColumnCoefficient
        beta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteResidualOscillationBound
          s beta) < 1 :=
  (Classical.choose_spec
    (exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
      s)).2.2 beta hbeta hcut

/-- On the strict canonical interval, every finite-volume/background physical
left-influence envelope has maximum column strictly below one. -/
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
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
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
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff_le_halfBarrierCutoff
        s)
  have hUniform :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperature_remoteResidualOscillationUniformBound
      N hN s hs beta hbeta hHalfCut
  have hGate :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff_spec
      s beta hbeta hcut
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_maximumColumn_lt_one_of_uniformResidual
      N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteResidualOscillationBound
        s beta)
      hUniform hGate H A

/-- The strict canonical interval gives volume-independent full-sweep
exponential contraction of the physical influence envelope. -/
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
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
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
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteResidualOscillationBound
                  s beta)) *
            (sweeps : ℝ)) *
        bound := by
  have hHalfCut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s :=
    hcut.trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff_le_halfBarrierCutoff
        s)
  have hRhoNonneg :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteResidualOscillationBound_nonneg
      s beta hs hbeta hHalfCut
  have hUniform :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperature_remoteResidualOscillationUniformBound
      N hN s hs beta hbeta hHalfCut
  have hGate :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff_spec
      s beta hbeta hcut
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_uniformFullSweepIterate_le_exp
      N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteResidualOscillationBound
        s beta)
      hRhoNonneg hUniform hGate H A
      variation hVariationNonneg bound hBoundNonneg hVariationBound sweeps source

end

end MGAP4D.MathlibAnalytic
