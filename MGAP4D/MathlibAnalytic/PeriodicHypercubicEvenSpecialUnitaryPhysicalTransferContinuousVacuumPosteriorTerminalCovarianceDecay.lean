import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorRandomScanBlockIterateBridge
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorFiniteResponseBootstrap
import Mathlib.Tactic

/-!
# Geometric decay of the posterior terminal covariance remainder

The finite covariance telescope of PR #5168 and bootstrap of PR #5169 leave

  Cov_pi(L_s, R^M F_t)

as the only terminal remainder.  PRs #5172--#5174 give a fixed-volume Doeblin
block contraction, and the exact kernel/BCF bridge identifies that block
dynamics with the very same random-scan observable used in #5169.

For the canonical all-link block length n and rho = 1 - delta,

  |Cov_pi(L_s, R^(k n) F_t)|
    <= ||L_s|| * rho^k * (exp(8 beta) - exp(-8 beta))
    -> 0.

The final theorem substitutes this generated envelope directly into #5169.
Thus the terminal-covariance hypothesis is no longer an external assumption at
fixed finite volume.  The Doeblin coefficient still depends on volume, so no
volume-uniform or continuum mixing claim is made.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory Topology

noncomputable section

local instance posteriorTerminalCovarianceSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance posteriorTerminalCovarianceTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance posteriorTerminalCovarianceCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance posteriorTerminalCovarianceSecondCountable
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance posteriorTerminalCovarianceMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance posteriorTerminalCovarianceBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- A pairwise oscillation bound on the right observable controls posterior
covariance by the sup norm of the left observable. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance_abs_le_norm_mul_pairwiseOscillation
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (F G : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (R : ℝ)
    (hR : 0 ≤ R)
    (hOsc :
      ∀ A C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        |G A - G C| ≤ R) :
    |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
        H N hN beta hbeta B F G| ≤
      ‖F‖ * R := by
  let mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
      H N hN beta hbeta B
  let mG :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
      H N hN beta hbeta B G
  letI : IsProbabilityMeasure mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure_isProbabilityMeasure
      H N hN beta hbeta B
  have hFInt : Integrable (fun A => F A) mu :=
    F.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hGInt : Integrable (fun A => G A) mu :=
    G.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hFGInt : Integrable (fun A => F A * G A) mu :=
    (F.continuous.mul G.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hFmGInt : Integrable (fun A => F A * mG) mu :=
    (F.continuous.mul continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hCentered (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
      |G A - mG| ≤ R := by
    have hConstInt :
        Integrable
          (fun _X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
            G A)
          mu :=
      integrable_const (G A)
    have hDiffInt :
        Integrable
          (fun X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
            G A - G X)
          mu :=
      hConstInt.sub' hGInt
    have hAbsDiffInt :
        Integrable
          (fun X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
            |G A - G X|)
          mu := by
      simpa [Real.norm_eq_abs] using hDiffInt.norm
    have hRInt :
        Integrable
          (fun _X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N => R)
          mu :=
      integrable_const R
    change |G A - ∫ X, G X ∂mu| ≤ R
    calc
      |G A - ∫ X, G X ∂mu| =
          |(∫ _X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
              G A ∂mu) -
            ∫ X, G X ∂mu| := by simp
      _ =
          |∫ X, G A - G X ∂mu| := by
        rw [integral_sub hConstInt hGInt]
      _ ≤
          ∫ X, |G A - G X| ∂mu :=
        abs_integral_le_integral_abs
      _ ≤
          ∫ _X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
            R ∂mu := by
        apply integral_mono hAbsDiffInt hRInt
        intro X
        exact hOsc A X
      _ = R := by simp
  have hIdentity :
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
          H N hN beta hbeta B F G =
        ∫ A, F A * (G A - mG) ∂mu := by
    unfold
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
    change
      (∫ A, F A * G A ∂mu) -
          (∫ A, F A ∂mu) * mG =
        ∫ A, F A * (G A - mG) ∂mu
    calc
      (∫ A, F A * G A ∂mu) -
          (∫ A, F A ∂mu) * mG =
        (∫ A, F A * G A ∂mu) -
          ∫ A, F A * mG ∂mu := by
            rw [integral_mul_const]
      _ =
        ∫ A, (F A * G A - F A * mG) ∂mu := by
          rw [integral_sub hFGInt hFmGInt]
      _ =
        ∫ A, F A * (G A - mG) ∂mu := by
          apply integral_congr_ae
          filter_upwards with A
          ring
  have hCenteredProductInt :
      Integrable (fun A => F A * (G A - mG)) mu :=
    (F.continuous.mul (G.continuous.sub continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hAbsCenteredProductInt :
      Integrable (fun A => |F A * (G A - mG)|) mu := by
    simpa [Real.norm_eq_abs] using hCenteredProductInt.norm
  have hBoundInt :
      Integrable
        (fun _A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          ‖F‖ * R)
        mu :=
    integrable_const (‖F‖ * R)
  rw [hIdentity]
  calc
    |∫ A, F A * (G A - mG) ∂mu| ≤
        ∫ A, |F A * (G A - mG)| ∂mu :=
      abs_integral_le_integral_abs
    _ ≤
        ∫ _A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
          ‖F‖ * R ∂mu := by
      apply integral_mono hAbsCenteredProductInt hBoundInt
      intro A
      change |F A * (G A - mG)| ≤ ‖F‖ * R
      rw [abs_mul]
      exact
        mul_le_mul
          (F.norm_coe_le_norm A)
          (hCentered A)
          (abs_nonneg _)
          (norm_nonneg F)
    _ = ‖F‖ * R := by simp

/-- Every posterior local Wilson factor has the global pairwise oscillation
width exp(8 beta) - exp(-8 beta). -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF_pairwise_abs_sub_le_width
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    |periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H N beta B target g A -
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H N beta B target g C| ≤
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
        beta := by
  have hALower :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_exp_neg_eight_mul_le
      H N hN beta hbeta A B target g
  have hAUpper :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_le_exp_eight_mul
      H N hN beta hbeta A B target g
  have hCLower :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_exp_neg_eight_mul_le
      H N hN beta hbeta C B target g
  have hCUpper :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_le_exp_eight_mul
      H N hN beta hbeta C B target g
  simp only [
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF_apply]
  unfold
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
  rw [abs_le]
  constructor <;> linarith

/-- Canonical centered random-scan state generated by one target-local factor. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorTargetLocalFactorCenteredState
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanCenteredState
      H N :=
  ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationBound
      H N hN beta hbeta B target g).toCenteredVariationProfile).toRandomScanCenteredState

/-- Uniform-in-target-value terminal covariance envelope along complete
posterior random-scan blocks. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorBlockTerminalCovarianceEnvelope
    (H N : ℕ)
    (beta : ℝ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (k : ℕ) : ℝ :=
  ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
      H N beta B source sourceValue‖ *
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMass
        H beta).toReal ^ k *
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
        beta)

/-- The block terminal covariance envelope is nonnegative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorBlockTerminalCovarianceEnvelope_nonneg
    (H N : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (k : ℕ) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorBlockTerminalCovarianceEnvelope
        H N beta B source sourceValue k := by
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorBlockTerminalCovarianceEnvelope
  exact mul_nonneg (norm_nonneg _)
    (mul_nonneg (pow_nonneg ENNReal.toReal_nonneg _)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth_nonneg
        beta hbeta))

/-- The exact terminal covariance appearing in #5169 decays geometrically
along complete posterior random-scan blocks. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_localFactor_randomScan_block_terminalCovariance_abs_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue g : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (k : ℕ) :
    |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
        H N hN beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H N beta B source sourceValue)
        ((periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorTargetLocalFactorCenteredState
            H N hN beta hbeta B target g).randomScanIterate D
          (k *
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
              H).length)).observable| ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorBlockTerminalCovarianceEnvelope
        H N beta B source sourceValue k := by
  let S :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorTargetLocalFactorCenteredState
      H N hN beta hbeta B target g
  let L :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
      H N beta B source sourceValue
  let width :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
      beta
  let rho : ℝ :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMass
      H beta).toReal
  have hWidth : 0 ≤ width := by
    dsimp [width]
    exact
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth_nonneg
        beta hbeta
  have hInitialOsc :
      ∀ A C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        |S.observable A - S.observable C| ≤ width := by
    intro A C
    dsimp [
      S,
      width,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorTargetLocalFactorCenteredState]
    exact
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF_pairwise_abs_sub_le_width
        H N hN beta hbeta B target g A C
  have hBlockOsc :
      ∀ A C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        |(S.randomScanIterate D
            (k *
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
                H).length)).observable A -
          (S.randomScanIterate D
            (k *
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
                H).length)).observable C| ≤
          rho ^ k * width := by
    intro A C
    rw [
      ← periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockExpectationIterate_eq_centeredStateIterate_mul_scheduleLength
        S D k A,
      ← periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockExpectationIterate_eq_centeredStateIterate_mul_scheduleLength
        S D k C]
    dsimp [rho]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockExpectationIterate_difference_abs_le_pow_residualMass_mul
        H N hN beta hbeta B S.observable
        S.observable.continuous.stronglyMeasurable
        width hWidth hInitialOsc k A C
  have hRNonneg : 0 ≤ rho ^ k * width :=
    mul_nonneg (pow_nonneg ENNReal.toReal_nonneg _) hWidth
  have hCov :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance_abs_le_norm_mul_pairwiseOscillation
      H N hN beta hbeta B L
      ((S.randomScanIterate D
        (k *
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
            H).length)).observable)
      (rho ^ k * width) hRNonneg hBlockOsc
  simpa [
    S,
    L,
    rho,
    width,
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorBlockTerminalCovarianceEnvelope
  ] using hCov

/-- The generated terminal covariance envelope tends to zero at every fixed
finite volume. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorBlockTerminalCovarianceEnvelope_tendsto_zero
    (H N : ℕ)
    (beta : ℝ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Tendsto
      (fun k =>
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorBlockTerminalCovarianceEnvelope
          H N beta B source sourceValue k)
      atTop
      (𝓝 0) := by
  let Lnorm : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
      H N beta B source sourceValue‖
  let width : ℝ :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
      beta
  have hPow :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMass_toReal_pow_tendsto_zero
      H beta
  have hMul :
      Tendsto
        (fun k : ℕ =>
          Lnorm *
            ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMass
              H beta).toReal ^ k * width))
        atTop
        (𝓝 (Lnorm * (0 * width))) :=
    tendsto_const_nhds.mul (hPow.mul_const width)
  simpa [
    Lnorm,
    width,
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorBlockTerminalCovarianceEnvelope
  ] using hMul

/-- The actual terminal covariance itself converges to zero along complete
posterior random-scan blocks. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_localFactor_randomScan_block_terminalCovariance_tendsto_zero
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Tendsto
      (fun k =>
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
          H N hN beta hbeta B
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
            H N beta B source sourceValue)
          ((periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorTargetLocalFactorCenteredState
              H N hN beta hbeta B target g).randomScanIterate D
            (k *
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
                H).length)).observable)
      atTop
      (𝓝 0) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hBound :
      ∀ k : ℕ,
        dist
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
            H N hN beta hbeta B
            (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
              H N beta B source sourceValue)
            ((periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorTargetLocalFactorCenteredState
                H N hN beta hbeta B target g).randomScanIterate D
              (k *
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
                  H).length)).observable)
          0 ≤
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorBlockTerminalCovarianceEnvelope
          H N beta B source sourceValue k := by
    intro k
    simpa [Real.dist_eq] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_localFactor_randomScan_block_terminalCovariance_abs_le
        H N hN beta hbeta B D target source sourceValue g k
  exact
    squeeze_zero
      (fun _ => dist_nonneg)
      hBound
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorBlockTerminalCovarianceEnvelope_tendsto_zero
        H N beta B source sourceValue)

/-- Fixed-volume terminal remainder closure for the finite response bootstrap:
the terminal envelope required by #5169 is generated explicitly by the
posterior Doeblin block contraction, with no external terminal-covariance
assumption. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorTargetExpectationResponseBound_of_blockDoeblinTerminalDecay
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (k : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorTargetExpectationResponseBound
      H N hN beta hbeta B target source sourceValue
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFiniteBootstrapResponseRadius
        D target source
        (k *
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
            H).length)
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorBlockTerminalCovarianceEnvelope
          H N beta B source sourceValue k)) := by
  have hEdge :
      0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) :=
    Fintype.card_pos_iff.mpr
      ⟨(⟨(0 : PeriodicHypercubicEvenVertex H), by
          simp [periodicHypercubicEvenOnPrimaryReflectionPlane]⟩,
        ⟨(1 : PeriodicHypercubicAxis), by norm_num⟩)⟩
  apply
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorTargetExpectationResponseBound_of_finiteRandomScanTerminalCovariance
      D target source sourceValue hEdge
      (k *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
          H).length)
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorBlockTerminalCovarianceEnvelope
        H N beta B source sourceValue k)
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorBlockTerminalCovarianceEnvelope_nonneg
        H N beta hbeta B source sourceValue k)
  intro g
  let F :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
      H N beta B target g
  let V :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationBound
      H N hN beta hbeta B target g
  let P := V.toCenteredVariationProfile
  let L :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
      H N beta B source sourceValue
  simpa [
    F,
    V,
    P,
    L,
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorTargetLocalFactorCenteredState
  ] using
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_localFactor_randomScan_block_terminalCovariance_abs_le
      H N hN beta hbeta B D target source sourceValue g k

end

end MathlibAnalytic
end MGAP4D
