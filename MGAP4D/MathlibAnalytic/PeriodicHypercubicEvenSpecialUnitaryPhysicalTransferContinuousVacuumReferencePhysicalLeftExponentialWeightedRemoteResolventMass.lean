import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferencePhysicalLeftExponentialWeightedEnvelopeColumn
import Mathlib.Tactic

/-!
# Exponentially weighted local-resolvent mass of the actual remote column

The local Harnack kernel already satisfies a volume-independent exponentially
weighted row/column coefficient

  rho_s = 18 * eta(beta) * s^2.

This file records the transpose-oriented weighted-L1 propagation that is needed
for the actual source-aligned remote column.  In particular, every finite local
Harnack resolvent amplifies the exponentially weighted mass of a nonnegative
forcing profile by at most the scalar geometric series, and hence by
`(1-rho_s)^{-1}` under the strict weighted threshold.

The final theorem is instantiated with the actual remote perturbation column.
No bound of the form `R_remote,weighted <= kappa * W` is assumed here, and no
coarse tagged eligible-row coefficient is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance physicalLeftExponentialWeightedRemoteResolventMassSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- One local-Harnack kernel application contracts exponentially weighted
transpose mass by the same coefficient as the weighted column estimate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel_exponentialWeightedMass_apply_le
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (hs : 1 ≤ s)
    (center : PeriodicHypercubicEvenSpatialSliceLink H)
    (w : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hwNonneg : ∀ source, 0 ≤ w source) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      finiteNonnegativeKernelApply
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
            H beta hbeta).influence
          w target *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target) ≤
      (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta *
        s ^ 2) *
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          w source *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s center source) := by
  classical
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
      H beta hbeta
  let W :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
      H s center
  let rho : ℝ :=
    18 *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
        beta *
      s ^ 2
  change
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      finiteNonnegativeKernelApply K.influence w target * W target) ≤
      rho * ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
        w source * W source
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
        w source * (rho * W source) := by
      apply Finset.sum_le_sum
      intro source _hSource
      apply mul_le_mul_of_nonneg_left _ (hwNonneg source)
      simpa [K, W, rho] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel_exponentialWeightedColumnSum_le
          H beta hbeta s hs center source
    _ =
      rho *
        ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          w source * W source := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro source _hSource
      ring

/-- Every power of the local Harnack kernel contracts exponentially weighted
transpose mass by the corresponding power of `rho_s`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackPowerApply_exponentialWeightedMass_le
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (hs : 1 ≤ s)
    (center : PeriodicHypercubicEvenSpatialSliceLink H)
    (w : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hwNonneg : ∀ source, 0 ≤ w source)
    (d : ℕ) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      finiteNonnegativeKernelPowerApply
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
            H beta hbeta).influence
          w d target *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target) ≤
      (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta *
        s ^ 2) ^ d *
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          w source *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s center source) := by
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
      H beta hbeta
  let W :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
      H s center
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
  have hRho : 0 ≤ rho := by
    dsimp [rho]
    positivity
  change
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      finiteNonnegativeKernelPowerApply K.influence w d target * W target) ≤
      rho ^ d *
        ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          w source * W source
  induction d with
  | zero =>
      simp
  | succ d ih =>
      have hIterNonneg :
          ∀ source : PeriodicHypercubicEvenSpatialSliceLink H,
            0 ≤ finiteNonnegativeKernelPowerApply K.influence w d source := by
        intro source
        exact
          finiteNonnegativeKernelPowerApply_nonneg
            K.influence K.influence_nonneg w hwNonneg d source
      have hStep :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel_exponentialWeightedMass_apply_le
          H beta hbeta s hs center
          (finiteNonnegativeKernelPowerApply K.influence w d)
          hIterNonneg
      have hStep' :
          (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
            finiteNonnegativeKernelPowerApply K.influence w (d + 1) target * W target) ≤
            rho *
              (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
                finiteNonnegativeKernelPowerApply K.influence w d source * W source) := by
        simpa [K, W, rho] using hStep
      calc
        (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          finiteNonnegativeKernelPowerApply K.influence w (d + 1) target * W target) ≤
            rho *
              (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
                finiteNonnegativeKernelPowerApply K.influence w d source * W source) :=
          hStep'
        _ ≤
            rho *
              (rho ^ d *
                ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
                  w source * W source) :=
          mul_le_mul_of_nonneg_left ih hRho
        _ =
            rho ^ (d + 1) *
              ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
                w source * W source := by
          rw [pow_succ]
          ring

/-- Every finite local-Harnack partial resolvent amplifies exponentially
weighted transpose mass by at most the finite scalar geometric sum. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackPartialResolvent_exponentialWeightedMass_le_sum_pow_mul
    (H M : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (hs : 1 ≤ s)
    (center : PeriodicHypercubicEvenSpatialSliceLink H)
    (w : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hwNonneg : ∀ source, 0 ≤ w source) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      finiteNonnegativeKernelPartialResolvent
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
            H beta hbeta).influence
          w M target *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target) ≤
      (∑ d ∈ Finset.range M,
        (18 *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
              beta *
          s ^ 2) ^ d) *
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          w source *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s center source) := by
  rw [show
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      finiteNonnegativeKernelPartialResolvent
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
            H beta hbeta).influence
          w M target *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target) =
      ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        (∑ d ∈ Finset.range M,
          finiteNonnegativeKernelPowerApply
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
              H beta hbeta).influence
            w d target) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
            H s center target by
      apply Finset.sum_congr rfl
      intro target _hTarget
      rw [finiteNonnegativeKernelPartialResolvent_eq_sum_powerApply_explicit]]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    (∑ d ∈ Finset.range M,
      ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        finiteNonnegativeKernelPowerApply
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
              H beta hbeta).influence
            w d target *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
            H s center target) ≤
      ∑ d ∈ Finset.range M,
        (18 *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
              beta *
          s ^ 2) ^ d *
          (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
            w source *
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
                H s center source) := by
      apply Finset.sum_le_sum
      intro d _hd
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackPowerApply_exponentialWeightedMass_le
          H beta hbeta s hs center w hwNonneg d
    _ =
      (∑ d ∈ Finset.range M,
        (18 *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
              beta *
          s ^ 2) ^ d) *
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          w source *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s center source) := by
      rw [Finset.sum_mul]

/-- Under the strict weighted local threshold, the finite local resolvent has
the volume-independent weighted-mass amplification factor `(1-rho_s)^{-1}`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackPartialResolvent_exponentialWeightedMass_le_one_div_one_sub_mul
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
    (center : PeriodicHypercubicEvenSpatialSliceLink H)
    (w : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hwNonneg : ∀ source, 0 ≤ w source) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      finiteNonnegativeKernelPartialResolvent
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
            H beta hbeta).influence
          w M target *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target) ≤
      (1 /
        (1 -
          18 *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
              beta *
          s ^ 2)) *
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          w source *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s center source) := by
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
      ∀ source : PeriodicHypercubicEvenSpatialSliceLink H,
        0 ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
            H s center source := by
    intro source
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_nonneg
        H s hsNonneg center source
  have hMassNonneg :
      0 ≤
        ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          w source *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s center source := by
    exact Finset.sum_nonneg fun source _ =>
      mul_nonneg (hwNonneg source) (hWeightNonneg source)
  have hFinite :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackPartialResolvent_exponentialWeightedMass_le_sum_pow_mul
      H M beta hbeta s hs center w hwNonneg
  calc
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      finiteNonnegativeKernelPartialResolvent
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
            H beta hbeta).influence
          w M target *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target) ≤
      (∑ d ∈ Finset.range M, rho ^ d) *
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          w source *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s center source) := by
      simpa [rho] using hFinite
    _ ≤
      (1 / (1 - rho)) *
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          w source *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s center source) := by
      exact
        mul_le_mul_of_nonneg_right
          (FiniteDistanceShellGeometricSum.sum_range_pow_le_one_div_one_sub
            rho hRho hRhoLt M)
          hMassNonneg
    _ =
      (1 /
        (1 -
          18 *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
              beta *
          s ^ 2)) *
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          w source *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s center source) := by
      rfl

/-- Concrete actual-remote instantiation: local Harnack propagation of one
source-aligned remote residual column has weighted mass bounded by the local
Green amplification factor times the actual weighted remote residual column
from the preceding theorem unit. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackPartialResolvent_remoteColumn_exponentialWeightedMass_le
    (H N M : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (s : ℝ)
    (hs : 1 ≤ s)
    (hWeightedThreshold :
      18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta *
        s ^ 2 < 1)
    (center source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      finiteNonnegativeKernelPartialResolvent
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
            H beta hbeta).influence
          (fun t =>
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationKernel
              H N hN beta hbeta A t source)
          M target *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target) ≤
      (1 /
        (1 -
          18 *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
              beta *
          s ^ 2)) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftExponentialWeightedRemoteResidualColumn
          H N hN beta hbeta A s center source := by
  have hRemoteNonneg :
      ∀ t : PeriodicHypercubicEvenSpatialSliceLink H,
        0 ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationKernel
            H N hN beta hbeta A t source := by
    intro t
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationKernel_nonneg
        H N hN beta hbeta A t source
  have hBase :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackPartialResolvent_exponentialWeightedMass_le_one_div_one_sub_mul
      H M beta hbeta s hs hWeightedThreshold center
      (fun t =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationKernel
          H N hN beta hbeta A t source)
      hRemoteNonneg
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftExponentialWeightedRemoteResidualColumn,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationKernel] using
    hBase

end

end MathlibAnalytic
end MGAP4D
