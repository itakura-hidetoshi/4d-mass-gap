import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFixedTargetPhysicalLeftExponentialWeightedPinAbsorption
import MGAP4D.MathlibAnalytic.FiniteNonnegativeKernelComparisonIteration
import Mathlib.Tactic

/-!
# Exponentially weighted fixed-target response bootstrap

The fixed-target physical envelope now has the volume-independent weighted
column decomposition

  column_W(source)
    <= (18 * eta(beta) * s^2 + eta(beta)) * W(source)
       + R_remote,W(source).

This file dualizes that column estimate against an arbitrary nonnegative
response profile.  The resulting operator estimate separates

* the volume-independent local-plus-pin weighted mass, and
* the actual remote weighted bilinear forcing.

It then sums a pointwise comparison

  w <= v + K_fixed w

against the growing exponential weight, producing the self-consistent weighted
bootstrap inequality needed for the actual fixed-target response route.

No estimate R_remote,W <= kappa * W is assumed, so the open remote coefficient
is not hidden or repackaged.  No coarse tagged eligible-row coefficient,
covariance decay, sweep contraction, Poincare/coercivity estimate, or mass-gap
statement is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance fixedTargetExponentialWeightedBootstrapSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The actual remote term appearing after dualizing the target-centered
weighted remote residual column against a response profile. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftExponentialWeightedRemoteBilinearForcing
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (s : ℝ)
    (center : PeriodicHypercubicEvenSpatialSliceLink H)
    (w : PeriodicHypercubicEvenSpatialSliceLink H → ℝ) : ℝ :=
  ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
    w source *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftExponentialWeightedRemoteResidualColumn
        H N hN beta hbeta A s center source

/-- A nonnegative response profile generates nonnegative actual remote weighted
bilinear forcing. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftExponentialWeightedRemoteBilinearForcing_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (s : ℝ)
    (hs : 0 ≤ s)
    (center : PeriodicHypercubicEvenSpatialSliceLink H)
    (w : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hwNonneg : ∀ source, 0 ≤ w source) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftExponentialWeightedRemoteBilinearForcing
        H N hN beta hbeta A s center w := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftExponentialWeightedRemoteBilinearForcing
  exact Finset.sum_nonneg fun source _ =>
    mul_nonneg
      (hwNonneg source)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftExponentialWeightedRemoteResidualColumn_nonneg
        H N hN beta hbeta A s hs center source)

/-- Dual weighted-mass form of the fixed-target column estimate.  The
local-plus-pin part is a scalar multiple of the weighted response mass, while
the actual remote residual remains an explicit bilinear forcing. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel_exponentialWeightedMass_apply_le_localPin_add_remote
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (s : ℝ)
    (hs : 1 ≤ s)
    (distinguishedTarget : PeriodicHypercubicEvenSpatialSliceLink H)
    (w : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hwNonneg : ∀ source, 0 ≤ w source) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      finiteNonnegativeKernelApply
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel
            H N hN beta hbeta A distinguishedTarget).influence
          w target *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s distinguishedTarget target) ≤
      (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta *
        s ^ 2 +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
          beta) *
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          w source *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s distinguishedTarget source) +
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftExponentialWeightedRemoteBilinearForcing
        H N hN beta hbeta A s distinguishedTarget w := by
  classical
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel
      H N hN beta hbeta A distinguishedTarget
  let W :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
      H s distinguishedTarget
  let alpha : ℝ :=
    18 *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
          beta *
      s ^ 2 +
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
        beta
  let remoteColumn :=
    fun source : PeriodicHypercubicEvenSpatialSliceLink H =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftExponentialWeightedRemoteResidualColumn
        H N hN beta hbeta A s distinguishedTarget source
  change
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      finiteNonnegativeKernelApply K.influence w target * W target) ≤
      alpha *
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          w source * W source) +
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftExponentialWeightedRemoteBilinearForcing
        H N hN beta hbeta A s distinguishedTarget w
  calc
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      finiteNonnegativeKernelApply K.influence w target * W target) =
      ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
        w source *
          (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
            K.influence target source * W target) := by
      unfold finiteNonnegativeKernelApply
      calc
        (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
            K.influence target source * w source) * W target) =
          ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
            ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
              w source * (K.influence target source * W target) := by
            apply Finset.sum_congr rfl
            intro target _hTarget
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro source _hSource
            ring
        _ =
          ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
            ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
              w source * (K.influence target source * W target) := by
            rw [Finset.sum_comm]
        _ =
          ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
            w source *
              (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
                K.influence target source * W target) := by
            apply Finset.sum_congr rfl
            intro source _hSource
            rw [Finset.mul_sum]
    _ ≤
      ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
        w source * (alpha * W source + remoteColumn source) := by
      apply Finset.sum_le_sum
      intro source _hSource
      apply mul_le_mul_of_nonneg_left _ (hwNonneg source)
      simpa [K, W, alpha, remoteColumn] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel_exponentialWeightedColumn_le_localPinCoefficient_add_remote
          H N hN beta hbeta A s hs distinguishedTarget source
    _ =
      alpha *
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          w source * W source) +
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftExponentialWeightedRemoteBilinearForcing
        H N hN beta hbeta A s distinguishedTarget w := by
      calc
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          w source * (alpha * W source + remoteColumn source)) =
          ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
            (alpha * (w source * W source) +
              w source * remoteColumn source) := by
            apply Finset.sum_congr rfl
            intro source _hSource
            ring
        _ =
          alpha *
            (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
              w source * W source) +
          ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
            w source * remoteColumn source := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        _ =
          alpha *
            (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
              w source * W source) +
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftExponentialWeightedRemoteBilinearForcing
            H N hN beta hbeta A s distinguishedTarget w := by
            unfold
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftExponentialWeightedRemoteBilinearForcing
            rfl

/-- Self-consistent weighted bootstrap.  Any nonnegative response profile
satisfying w <= v + K_fixed w has weighted mass bounded by direct forcing,
the volume-independent local-plus-pin feedback, and the explicit actual remote
bilinear forcing. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeft_exponentialWeightedBootstrap
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (s : ℝ)
    (hs : 1 ≤ s)
    (distinguishedTarget : PeriodicHypercubicEvenSpatialSliceLink H)
    (v w : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hwNonneg : ∀ source, 0 ≤ w source)
    (hComparison :
      ∀ target,
        w target ≤
          v target +
            finiteNonnegativeKernelApply
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel
                H N hN beta hbeta A distinguishedTarget).influence
              w target) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      w target *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s distinguishedTarget target) ≤
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        v target *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
            H s distinguishedTarget target) +
      (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta *
        s ^ 2 +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
          beta) *
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          w source *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s distinguishedTarget source) +
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftExponentialWeightedRemoteBilinearForcing
        H N hN beta hbeta A s distinguishedTarget w := by
  classical
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel
      H N hN beta hbeta A distinguishedTarget
  let W :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
      H s distinguishedTarget
  have hsNonneg : 0 ≤ s := le_trans (by norm_num) hs
  have hWeightNonneg : ∀ target, 0 ≤ W target := by
    intro target
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_nonneg
        H s hsNonneg distinguishedTarget target
  have hApply :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel_exponentialWeightedMass_apply_le_localPin_add_remote
      H N hN beta hbeta A s hs distinguishedTarget w hwNonneg
  calc
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      w target *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s distinguishedTarget target) ≤
      ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        (v target + finiteNonnegativeKernelApply K.influence w target) *
          W target := by
      apply Finset.sum_le_sum
      intro target _hTarget
      exact
        mul_le_mul_of_nonneg_right
          (by simpa [K] using hComparison target)
          (hWeightNonneg target)
    _ =
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        v target * W target) +
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        finiteNonnegativeKernelApply K.influence w target * W target) := by
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib]
    _ ≤
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        v target * W target) +
      ((18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta *
        s ^ 2 +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
          beta) *
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          w source * W source) +
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftExponentialWeightedRemoteBilinearForcing
        H N hN beta hbeta A s distinguishedTarget w) := by
      apply add_le_add_left
      simpa [K, W] using hApply
    _ =
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        v target *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
            H s distinguishedTarget target) +
      (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta *
        s ^ 2 +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
          beta) *
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          w source *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s distinguishedTarget source) +
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftExponentialWeightedRemoteBilinearForcing
        H N hN beta hbeta A s distinguishedTarget w := by
      rfl

end

end MathlibAnalytic
end MGAP4D
