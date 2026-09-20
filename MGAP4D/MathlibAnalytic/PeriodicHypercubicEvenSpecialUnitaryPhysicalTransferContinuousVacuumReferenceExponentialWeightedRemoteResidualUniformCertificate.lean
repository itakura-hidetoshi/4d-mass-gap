import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFixedTargetPhysicalLeftExponentialWeightedBootstrap
import Mathlib.Tactic

/-!
# Uniform certificate for exponentially weighted remote residuals

The fixed-target weighted response algebra has already reduced the physical
envelope to

  local+pin coefficient
    = 18 * eta(beta) * s^2 + eta(beta)

plus the actual target-centered exponentially weighted remote residual.

This file isolates the remaining analytic input as a single uniform
certificate

  R_remote,W(A; center, source) <= kappa * W_center(source)

uniformly in finite volume, background configuration, center and source.

Conditional on that certificate, the full fixed-target weighted envelope has
coefficient

  c_s = 18 * eta(beta) * s^2 + eta(beta) + kappa,

and every nonnegative response profile satisfying

  w <= v + K_fixed w

obeys the scalar weighted bootstrap

  M_s(w) <= M_s(v) + c_s * M_s(w).

Under c_s < 1 this closes to

  M_s(w) <= M_s(v) / (1 - c_s).

No existence or numerical estimate for kappa is asserted here.  Thus the
remaining analytic obstruction is exposed rather than hidden.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance exponentialWeightedRemoteResidualUniformCertificateSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Uniform exponentially weighted remote-residual certificate.  This is the
weighted analogue of the previously formalized unweighted uniform residual
certificate, but with the center/source weight retained pointwise. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceExponentialWeightedRemoteResidualUniformBound
    (N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s kappa : ℝ) : Prop :=
  ∀ H : ℕ,
    ∀ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
      ∀ center source : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftExponentialWeightedRemoteResidualColumn
            H N hN beta hbeta A s center source ≤
          kappa *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s center source

/-- Uniform coefficient of the full target-centered exponentially weighted
fixed-target envelope. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformExponentialWeightedEnvelopeCoefficient
    (beta s kappa : ℝ) : ℝ :=
  18 *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
        beta *
      s ^ 2 +
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
      beta +
    kappa

/-- Nonnegative inputs give a nonnegative uniform weighted envelope
coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformExponentialWeightedEnvelopeCoefficient_nonneg
    (beta s kappa : ℝ)
    (hbeta : 0 ≤ beta)
    (hkappa : 0 ≤ kappa) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformExponentialWeightedEnvelopeCoefficient
        beta s kappa := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformExponentialWeightedEnvelopeCoefficient
  have hEta :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
          beta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence_nonneg
      beta hbeta
  positivity

/-- A uniform weighted remote certificate turns the concrete fixed-target
weighted column estimate into one scalar coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel_exponentialWeightedColumn_le_uniform
    (N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s kappa : ℝ)
    (hs : 1 ≤ s)
    (hUniform :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceExponentialWeightedRemoteResidualUniformBound
        N hN beta hbeta s kappa)
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (center source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel
          H N hN beta hbeta A center).influence target source *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformExponentialWeightedEnvelopeCoefficient
          beta s kappa *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center source := by
  have hBase :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel_exponentialWeightedColumn_le_localPinCoefficient_add_remote
      H N hN beta hbeta A s hs center source
  have hRemote := hUniform H A center source
  calc
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel
          H N hN beta hbeta A center).influence target source *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target) ≤
      (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta *
        s ^ 2 +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
          beta) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center source +
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftExponentialWeightedRemoteResidualColumn
        H N hN beta hbeta A s center source := hBase
    _ ≤
      (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta *
        s ^ 2 +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
          beta) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center source +
      kappa *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center source := by
      exact add_le_add (le_refl _) hRemote
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformExponentialWeightedEnvelopeCoefficient
          beta s kappa *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center source := by
      unfold
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformExponentialWeightedEnvelopeCoefficient
      ring

/-- The actual remote weighted bilinear forcing is bounded by kappa times the
weighted response mass under the uniform remote certificate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftExponentialWeightedRemoteBilinearForcing_le_uniform
    (N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s kappa : ℝ)
    (hUniform :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceExponentialWeightedRemoteResidualUniformBound
        N hN beta hbeta s kappa)
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (center : PeriodicHypercubicEvenSpatialSliceLink H)
    (w : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hwNonneg : ∀ source, 0 ≤ w source) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftExponentialWeightedRemoteBilinearForcing
        H N hN beta hbeta A s center w ≤
      kappa *
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          w source *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s center source) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftExponentialWeightedRemoteBilinearForcing
  calc
    (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
      w source *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftExponentialWeightedRemoteResidualColumn
          H N hN beta hbeta A s center source) ≤
      ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
        w source *
          (kappa *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s center source) := by
      apply Finset.sum_le_sum
      intro source _hSource
      exact
        mul_le_mul_of_nonneg_left
          (hUniform H A center source)
          (hwNonneg source)
    _ =
      kappa *
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          w source *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s center source) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro source _hSource
      ring

/-- Under the uniform weighted remote certificate, one fixed-target envelope
application contracts weighted mass by the single coefficient c_s. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel_exponentialWeightedMass_apply_le_uniform
    (N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s kappa : ℝ)
    (hs : 1 ≤ s)
    (hUniform :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceExponentialWeightedRemoteResidualUniformBound
        N hN beta hbeta s kappa)
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (center : PeriodicHypercubicEvenSpatialSliceLink H)
    (w : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hwNonneg : ∀ source, 0 ≤ w source) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      finiteNonnegativeKernelApply
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel
            H N hN beta hbeta A center).influence
          w target *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformExponentialWeightedEnvelopeCoefficient
          beta s kappa *
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          w source *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s center source) := by
  have hApply :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel_exponentialWeightedMass_apply_le_localPin_add_remote
      H N hN beta hbeta A s hs center w hwNonneg
  have hRemote :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftExponentialWeightedRemoteBilinearForcing_le_uniform
      N hN beta hbeta s kappa hUniform H A center w hwNonneg
  calc
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      finiteNonnegativeKernelApply
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel
            H N hN beta hbeta A center).influence
          w target *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target) ≤
      (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta *
        s ^ 2 +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
          beta) *
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          w source *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s center source) +
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftExponentialWeightedRemoteBilinearForcing
        H N hN beta hbeta A s center w := hApply
    _ ≤
      (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta *
        s ^ 2 +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
          beta) *
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          w source *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s center source) +
      kappa *
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          w source *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s center source) := by
      exact add_le_add (le_refl _) hRemote
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformExponentialWeightedEnvelopeCoefficient
          beta s kappa *
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          w source *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s center source) := by
      unfold
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformExponentialWeightedEnvelopeCoefficient
      ring

/-- Uniform scalar form of the fixed-target weighted response bootstrap. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeft_exponentialWeightedBootstrap_le_direct_add_uniformFeedback
    (N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s kappa : ℝ)
    (hs : 1 ≤ s)
    (hUniform :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceExponentialWeightedRemoteResidualUniformBound
        N hN beta hbeta s kappa)
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (center : PeriodicHypercubicEvenSpatialSliceLink H)
    (v w : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hwNonneg : ∀ source, 0 ≤ w source)
    (hComparison :
      ∀ target,
        w target ≤
          v target +
            finiteNonnegativeKernelApply
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel
                H N hN beta hbeta A center).influence
              w target) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      w target *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target) ≤
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        v target *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
            H s center target) +
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformExponentialWeightedEnvelopeCoefficient
          beta s kappa *
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          w source *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s center source) := by
  have hBootstrap :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeft_exponentialWeightedBootstrap
      H N hN beta hbeta A s hs center v w hwNonneg hComparison
  have hRemote :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftExponentialWeightedRemoteBilinearForcing_le_uniform
      N hN beta hbeta s kappa hUniform H A center w hwNonneg
  calc
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      w target *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target) ≤
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        v target *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
            H s center target) +
      (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta *
        s ^ 2 +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
          beta) *
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          w source *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s center source) +
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftExponentialWeightedRemoteBilinearForcing
        H N hN beta hbeta A s center w := hBootstrap
    _ ≤
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        v target *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
            H s center target) +
      (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta *
        s ^ 2 +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
          beta) *
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          w source *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s center source) +
      kappa *
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          w source *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s center source) := by
      exact add_le_add (le_refl _) hRemote
    _ =
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        v target *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
            H s center target) +
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformExponentialWeightedEnvelopeCoefficient
          beta s kappa *
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          w source *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s center source) := by
      unfold
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformExponentialWeightedEnvelopeCoefficient
      ring

/-- Resolvent closure of the uniform weighted bootstrap. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeft_exponentialWeightedBootstrap_le_direct_div_one_sub_uniformCoefficient
    (N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s kappa : ℝ)
    (hs : 1 ≤ s)
    (hUniform :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceExponentialWeightedRemoteResidualUniformBound
        N hN beta hbeta s kappa)
    (hGate :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformExponentialWeightedEnvelopeCoefficient
          beta s kappa < 1)
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (center : PeriodicHypercubicEvenSpatialSliceLink H)
    (v w : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hwNonneg : ∀ source, 0 ≤ w source)
    (hComparison :
      ∀ target,
        w target ≤
          v target +
            finiteNonnegativeKernelApply
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel
                H N hN beta hbeta A center).influence
              w target) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      w target *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target) ≤
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        v target *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
            H s center target) /
        (1 -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformExponentialWeightedEnvelopeCoefficient
            beta s kappa) := by
  let M : ℝ :=
    ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      w target *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target
  let V : ℝ :=
    ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      v target *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target
  let c : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformExponentialWeightedEnvelopeCoefficient
      beta s kappa
  have hScalar : M ≤ V + c * M := by
    simpa [M, V, c] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeft_exponentialWeightedBootstrap_le_direct_add_uniformFeedback
        N hN beta hbeta s kappa hs hUniform H A center v w hwNonneg hComparison
  have hOneMinus : 0 < 1 - c := sub_pos.mpr (by simpa [c] using hGate)
  have hRearranged : M - c * M ≤ V := by
    exact (sub_le_iff_le_add).2 hScalar
  apply (le_div_iff₀ hOneMinus).2
  calc
    M * (1 - c) = M - c * M := by ring
    _ ≤ V := hRearranged

end

end MathlibAnalytic
end MGAP4D
