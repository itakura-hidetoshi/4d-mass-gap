import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferencePhysicalLeftLocalHarnackExponentialWeightedRow
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferencePhysicalLeftLocalHarnackSingletonRemoteResolvent
import Mathlib.Tactic

/-!
# Exponentially weighted powers and resolvent for the physical local Harnack kernel

The preceding theorem unit proves that, for the growing base-L1 weight

  W_center(source) = s ^ baseL1Distance(center, source),

the actual local physical Harnack kernel satisfies

  K_local W_center <= rho_s W_center,

where

  rho_s = 18 * eta(beta) * s^2.

This file iterates that subinvariance without replacing the spatial weight by
an unweighted row norm.  Consequently every power satisfies

  K_local^d W_center <= rho_s^d W_center,

and, under rho_s < 1, every finite local Green truncation satisfies the
volume-independent bound

  G_local,M W_center <= (1-rho_s)^(-1) W_center.

Only the genuine local carrier is used.  No remote-response estimate,
covariance decay, physical sweep contraction, Poincare/coercivity inequality,
or mass-gap statement is assumed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance physicalLeftLocalHarnackExponentialWeightedResolventSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The exponentially weighted local-Harnack subinvariance from the preceding
unit iterates exactly through every finite kernel power. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackPowerApply_exponentialWeight_le
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (hs : 1 ≤ s)
    (center : PeriodicHypercubicEvenSpatialSliceLink H)
    (d : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    finiteNonnegativeKernelPowerApply
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
          H beta hbeta).influence
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center)
        d target ≤
      (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta *
        s ^ 2) ^ d *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target := by
  classical
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
      H beta hbeta
  let weight :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
      H s center
  let eta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
      beta
  let rho : ℝ := 18 * eta * s ^ 2
  change
    finiteNonnegativeKernelPowerApply K.influence weight d target ≤
      rho ^ d * weight target
  have hEta : 0 ≤ eta := by
    simpa [eta] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence_nonneg
        beta hbeta
  have hsNonneg : 0 ≤ s := le_trans (by norm_num) hs
  have hRho : 0 ≤ rho := by
    dsimp [rho]
    positivity
  induction d generalizing target with
  | zero =>
      simp
  | succ d ih =>
      calc
        finiteNonnegativeKernelPowerApply K.influence weight (d + 1) target =
            finiteNonnegativeKernelApply K.influence
              (finiteNonnegativeKernelPowerApply K.influence weight d) target := by
          rfl
        _ ≤ finiteNonnegativeKernelApply K.influence
              (fun source => rho ^ d * weight source) target :=
          finiteNonnegativeKernelApply_mono
            K.influence K.influence_nonneg
            (fun source => ih source) target
        _ = rho ^ d *
              finiteNonnegativeKernelApply K.influence weight target := by
          unfold finiteNonnegativeKernelApply
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro source _hsource
          ring
        _ ≤ rho ^ d * (rho * weight target) := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg hRho d)
          simpa [K, weight, rho, eta, finiteNonnegativeKernelApply] using
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel_exponentialWeightedRowSum_le
              H beta hbeta s hs center target
        _ = rho ^ (d + 1) * weight target := by
          rw [pow_succ]
          ring

/-- Every finite local-Harnack partial resolvent of the exponential weight is
bounded by the corresponding finite scalar geometric sum times the same
weight.  No strict threshold is needed for this finite statement. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackPartialResolvent_exponentialWeight_le_sum_pow_mul
    (H M : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (hs : 1 ≤ s)
    (center target : PeriodicHypercubicEvenSpatialSliceLink H) :
    finiteNonnegativeKernelPartialResolvent
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
          H beta hbeta).influence
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center)
        M target ≤
      (∑ d ∈ Finset.range M,
        (18 *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
              beta *
          s ^ 2) ^ d) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target := by
  rw [finiteNonnegativeKernelPartialResolvent_eq_sum_powerApply_explicit]
  calc
    (∑ d ∈ Finset.range M,
      finiteNonnegativeKernelPowerApply
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
          H beta hbeta).influence
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center)
        d target) ≤
      ∑ d ∈ Finset.range M,
        (18 *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
              beta *
          s ^ 2) ^ d *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
            H s center target := by
      apply Finset.sum_le_sum
      intro d _hd
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackPowerApply_exponentialWeight_le
          H beta hbeta s hs center d target
    _ =
      (∑ d ∈ Finset.range M,
        (18 *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
              beta *
          s ^ 2) ^ d) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target := by
      rw [Finset.sum_mul]

/-- Under the strict exponentially weighted threshold, every finite local
Green truncation is bounded uniformly in its depth by the reciprocal scalar
gap times the same growing base-L1 weight. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackPartialResolvent_exponentialWeight_le_one_div_one_sub_mul
    (H M : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (hs : 1 ≤ s)
    (hWeightedThreshold :
      18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta *
        s ^ 2 < 1)
    (center target : PeriodicHypercubicEvenSpatialSliceLink H) :
    finiteNonnegativeKernelPartialResolvent
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
          H beta hbeta).influence
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center)
        M target ≤
      (1 /
        (1 -
          18 *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
              beta *
          s ^ 2)) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target := by
  let rho : ℝ :=
    18 *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
        beta *
      s ^ 2
  have hEta :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
          beta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence_nonneg
      beta hbeta
  have hsNonneg : 0 ≤ s := le_trans (by norm_num) hs
  have hRho : 0 ≤ rho := by
    dsimp [rho]
    positivity
  have hRhoLt : rho < 1 := by
    simpa [rho] using hWeightedThreshold
  have hWeightNonneg :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_nonneg
      H s hsNonneg center target
  have hFinite :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackPartialResolvent_exponentialWeight_le_sum_pow_mul
      H M beta hbeta s hs center target
  calc
    finiteNonnegativeKernelPartialResolvent
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
          H beta hbeta).influence
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center)
        M target ≤
      (∑ d ∈ Finset.range M, rho ^ d) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target := by
      simpa [rho] using hFinite
    _ ≤
      (1 / (1 - rho)) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target := by
      exact
        mul_le_mul_of_nonneg_right
          (FiniteDistanceShellGeometricSum.sum_range_pow_le_one_div_one_sub
            rho hRho hRhoLt M)
          hWeightNonneg
    _ =
      (1 /
        (1 -
          18 *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
              beta *
          s ^ 2)) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target := by
      rfl

end

end MathlibAnalytic
end MGAP4D
