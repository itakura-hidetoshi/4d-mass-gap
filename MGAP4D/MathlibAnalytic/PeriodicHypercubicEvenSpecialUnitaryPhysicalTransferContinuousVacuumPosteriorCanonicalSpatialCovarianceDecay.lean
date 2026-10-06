import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorCanonicalFixedRightResponseBridge
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorResponseCovarianceBridge
import Mathlib.Tactic

/-!
# Actual posterior spatial covariance decay from the canonical response envelope

PR #5194 identifies the literal ordinary posterior target/source response with
a canonical fixed-right response and proves the source-centered base-L1 bound

  epsilon(target,source)
    <= Mbar(s,beta) / W_source(target).

The posterior response/covariance identity gives

  tiltedExpectation - baseExpectation
    = covariance / sourceMean.

The source local-factor mean is already bounded below by exp(-8 beta).  This
file adds the matching volume-independent upper bound exp(8 beta), reverses the
identity, and converts any ordinary expectation-response estimate epsilon into

  |Cov(L_target,L_source)| <= exp(8 beta) * epsilon.

Specializing to the actual canonical response from PR #5194 yields

  |Cov(L_target,L_source)|
    <= [exp(8 beta) * Mbar(s,beta)] / W_source(target)

for every plaquette-remote ordered pair.  Since

  W_source(target) = s ^ d_baseL1(source,target),

this is literal H- and N-independent spatial exponential covariance decay for
the continuous-vacuum posterior local factors on the existing canonical
high-temperature interval.

No identification of random-scan update time with Euclidean physical time,
spacing-scaled continuum generator theorem, H1-D5 exact descent, or complete
four-dimensional Yang--Mills mass-gap claim is made.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance posteriorCanonicalSpatialCovarianceTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance posteriorCanonicalSpatialCovarianceCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance posteriorCanonicalSpatialCovarianceSecondCountable
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance posteriorCanonicalSpatialCovarianceMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance posteriorCanonicalSpatialCovarianceBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The posterior mean of one target-local Boltzmann factor has the
volume-independent upper ceiling exp(8 beta). -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean_localFactor_le_exp_eight_mul
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
        H N hN beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H N beta B source sourceValue) ≤
      Real.exp (8 * beta) := by
  let mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
      H N hN beta hbeta B
  let L :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
      H N beta B source sourceValue
  letI : IsProbabilityMeasure mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure_isProbabilityMeasure
      H N hN beta hbeta B
  have hLInt : Integrable (fun A => L A) mu :=
    L.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hConstInt :
      Integrable
        (fun _A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          Real.exp (8 * beta))
        mu :=
    integrable_const _
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
  change
    (∫ A, L A ∂mu) ≤ Real.exp (8 * beta)
  calc
    (∫ A, L A ∂mu) ≤
        ∫ _A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
          Real.exp (8 * beta) ∂mu := by
      apply integral_mono hLInt hConstInt
      intro A
      simpa [L] using
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_le_exp_eight_mul
          H N hN beta hbeta A B source sourceValue
    _ = Real.exp (8 * beta) := by simp

/-- Any ordinary posterior target/source expectation-response bound epsilon
gives the reverse covariance estimate exp(8 beta) * epsilon. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance_abs_le_exp_eight_mul_of_expectationResponse
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue g : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (epsilon : ℝ)
    (hResponse :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorTargetExpectationResponseBound
        H N hN beta hbeta B target source sourceValue epsilon) :
    |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
        H N hN beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H N beta B target g)
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H N beta B source sourceValue)| ≤
      Real.exp (8 * beta) * epsilon := by
  let sourceMean :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
      H N hN beta hbeta B
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
        H N beta B source sourceValue)
  let cov :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
      H N hN beta hbeta B
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
        H N beta B target g)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
        H N beta B source sourceValue)
  let diff :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceTiltedTargetExpectation
        H N hN beta hbeta B target source sourceValue g -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorTargetExpectation
        H N hN beta hbeta B target g
  have hMeanLower :
      Real.exp (-8 * beta) ≤ sourceMean := by
    simpa [sourceMean] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean_localFactor_exp_neg_eight_mul_le
        H N hN beta hbeta B source sourceValue
  have hMeanPos : 0 < sourceMean :=
    lt_of_lt_of_le (Real.exp_pos _) hMeanLower
  have hMeanUpper :
      sourceMean ≤ Real.exp (8 * beta) := by
    simpa [sourceMean] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean_localFactor_le_exp_eight_mul
        H N hN beta hbeta B source sourceValue
  have hIdentity :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceTiltedTargetExpectation_sub_targetExpectation_eq_covariance_div_sourceMean
      H N hN beta hbeta B target source sourceValue g
  have hDiffDiv :
      diff = cov / sourceMean := by
    simpa [diff, cov, sourceMean] using hIdentity
  have hMul : diff * sourceMean = cov :=
    (eq_div_iff (ne_of_gt hMeanPos)).mp hDiffDiv
  have hCovEq : cov = sourceMean * diff := by
    calc
      cov = diff * sourceMean := hMul.symm
      _ = sourceMean * diff := by ring
  have hDiff :
      |diff| ≤ epsilon := by
    simpa [diff, abs_sub_comm] using hResponse g
  change |cov| ≤ Real.exp (8 * beta) * epsilon
  rw [hCovEq, abs_mul, abs_of_pos hMeanPos]
  exact
    mul_le_mul hMeanUpper hDiff
      (abs_nonneg diff) (Real.exp_pos _).le

/-- Volume-independent covariance prefactor inherited from the canonical
fixed-right response envelope. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapCovariancePrefactor
    (s beta : ℝ) : ℝ :=
  Real.exp (8 * beta) *
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap
      s beta

theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapCovariancePrefactor_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 1 ≤ s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapCovariancePrefactor
        s beta := by
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapCovariancePrefactor
  exact
    mul_nonneg (Real.exp_pos _).le
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap_nonneg
        H N hN s hs beta hbeta hcut)

/-- On the canonical high-temperature interval, every plaquette-remote pair of
actual posterior local factors has source-centered base-L1 exponential
covariance decay with an H- and N-independent prefactor. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrap_localFactorCovariance_abs_le_div_exponentialWeight
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 1 ≤ s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue g : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hNe : source ≠ target)
    (hRemote :
      ¬ periodicHypercubicEvenSpatialSlicePlaquetteLocal H target source) :
    |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
        H N hN beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H N beta B target g)
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H N beta B source sourceValue)| ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapCovariancePrefactor
          s beta /
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s source target := by
  let epsilon :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap
        s beta /
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
        H s source target
  have hResponse :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorTargetExpectationResponseBound
        H N hN beta hbeta B target source sourceValue epsilon := by
    simpa [epsilon] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorTargetExpectationResponseBound_of_canonicalFixedRightBootstrapEnvelope
        H N hN s hs beta hbeta hcut B target source sourceValue hNe hRemote
  have hCov :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance_abs_le_exp_eight_mul_of_expectationResponse
      H N hN beta hbeta B target source sourceValue g epsilon hResponse
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapCovariancePrefactor
  dsimp [epsilon] at hCov ⊢
  simpa [mul_div_assoc] using hCov

/-- Same covariance decay written explicitly as a power of the periodic
base-L1 separation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrap_localFactorCovariance_abs_le_baseL1Power
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 1 ≤ s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue g : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hNe : source ≠ target)
    (hRemote :
      ¬ periodicHypercubicEvenSpatialSlicePlaquetteLocal H target source) :
    |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
        H N hN beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H N beta B target g)
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H N beta B source sourceValue)| ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapCovariancePrefactor
          s beta /
        s ^
          periodicHypercubicEdgeBaseL1Distance
            (PeriodicHypercubicEvenSideLength H)
            (periodicHypercubicEvenSpatialSliceLinkEmbedding H source)
            (periodicHypercubicEvenSpatialSliceLinkEmbedding H target) := by
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
  ] using
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrap_localFactorCovariance_abs_le_div_exponentialWeight
      H N hN s hs beta hbeta hcut B target source sourceValue g hNe hRemote

end

end MathlibAnalytic
end MGAP4D
