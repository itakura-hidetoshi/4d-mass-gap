import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferencePhysicalLeftLocalGreenRemoteColumnMass
import Mathlib.Tactic

/-!
# Base-L1 weighted local Green convolution with the remote physical residual

The preceding local-Green reduction bounded the remote perturbation by a
global L1 profile mass.  That estimate is useful but erases the spatial
location at which the remote perturbation enters the local Green kernel.

This file keeps that location explicit.

For the actual local Harnack kernel define the canonical propagation depth

  floor(baseL1Distance(target, source) / 2).

The finite local Green kernel from any source to any target is bounded by

  rho_local ^ depth / (1 - rho_local).

Consequently the local Green response to the physical remote forcing is
bounded by the spatial convolution

  sum_source
    [sum_mid localGreenWeight(target, mid) * remoteResidual(source, mid)]
    * w(source).

Thus the remaining remote obstruction is a target/source weighted remote
column, not an unweighted global L1 norm.  No covariance-decay hypothesis is
used and no remote uniform certificate is assumed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance physicalLeftLocalGreenWeightedRemoteConvolutionSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Finite kernel application commutes with a sum over any finite index type. -/
theorem finiteNonnegativeKernelApply_fintype_sum
    {ι κ : Type}
    [Fintype ι]
    [Fintype κ]
    (kernel : ι → ι → ℝ)
    (f : κ → ι → ℝ)
    (target : ι) :
    finiteNonnegativeKernelApply
        kernel
        (fun source => ∑ j : κ, f j source)
        target =
      ∑ j : κ,
        finiteNonnegativeKernelApply kernel (f j) target := by
  classical
  unfold finiteNonnegativeKernelApply
  calc
    (∑ source : ι,
      kernel target source * (∑ j : κ, f j source)) =
        ∑ source : ι,
          ∑ j : κ, kernel target source * f j source := by
      apply Finset.sum_congr rfl
      intro source _hsource
      rw [Finset.mul_sum]
    _ =
        ∑ j : κ,
          ∑ source : ι, kernel target source * f j source := by
      rw [Finset.sum_comm]
    _ =
        ∑ j : κ,
          finiteNonnegativeKernelApply kernel (f j) target := by
      rfl

/-- Finite partial resolvents commute with a sum over any finite index type. -/
theorem finiteNonnegativeKernelPartialResolvent_fintype_sum
    {ι κ : Type}
    [Fintype ι]
    [Fintype κ]
    (kernel : ι → ι → ℝ)
    (f : κ → ι → ℝ)
    (n : ℕ)
    (target : ι) :
    finiteNonnegativeKernelPartialResolvent
        kernel
        (fun source => ∑ j : κ, f j source)
        n target =
      ∑ j : κ,
        finiteNonnegativeKernelPartialResolvent kernel (f j) n target := by
  classical
  induction n generalizing target with
  | zero =>
      simp
  | succ n ih =>
      simp only [finiteNonnegativeKernelPartialResolvent_succ]
      have hPrevious :
          finiteNonnegativeKernelPartialResolvent
              kernel
              (fun source => ∑ j : κ, f j source)
              n =
            fun source =>
              ∑ j : κ,
                finiteNonnegativeKernelPartialResolvent
                  kernel (f j) n source := by
        funext source
        exact ih source
      rw [hPrevious]
      rw [finiteNonnegativeKernelApply_fintype_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _hj
      rfl

/-- Every profile is the finite sum of its singleton components. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnack_sum_singletonForcing_eq
    (H : ℕ)
    (b : PeriodicHypercubicEvenSpatialSliceLink H → ℝ) :
    (fun target =>
      ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackSingletonForcing
          source (b source) target) =
      b := by
  classical
  funext target
  simp [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackSingletonForcing]

/-- The generic local partial resolvent is exactly the source sum of the
finite local-Harnack resolvent entries against the forcing profile. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackPartialResolvent_eq_sum_finiteResolventEntry_mul
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (M : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    finiteNonnegativeKernelPartialResolvent
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
          H beta hbeta).influence
        b M target =
      ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackFiniteResolventEntry
            H beta hbeta M target source *
          b source := by
  classical
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
      H beta hbeta
  let singleton :=
    fun source : PeriodicHypercubicEvenSpatialSliceLink H =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackSingletonForcing
        source (b source)
  have hDecompose :
      (fun t =>
        ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          singleton source t) = b := by
    simpa [singleton] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnack_sum_singletonForcing_eq
        H b
  calc
    finiteNonnegativeKernelPartialResolvent
        K.influence b M target =
      finiteNonnegativeKernelPartialResolvent
        K.influence
        (fun t =>
          ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
            singleton source t)
        M target := by
      rw [hDecompose]
    _ =
      ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
        finiteNonnegativeKernelPartialResolvent
          K.influence (singleton source) M target := by
      exact
        finiteNonnegativeKernelPartialResolvent_fintype_sum
          K.influence singleton M target
    _ =
      ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackFiniteResolventEntry
            H beta hbeta M target source *
          b source := by
      apply Finset.sum_congr rfl
      intro source _hsource
      simpa [K, singleton] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackPartialResolvent_singleton_eq_finiteResolventEntry_mul
          H beta hbeta M target source (b source)

/-- Canonical number of two-unit local-Harnack propagation steps supplied by
the embedded periodic base-L1 distance. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1Depth
    (H : ℕ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) : ℕ :=
  periodicHypercubicEdgeBaseL1Distance
      (PeriodicHypercubicEvenSideLength H)
      (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)
      (periodicHypercubicEvenSpatialSliceLinkEmbedding H source) /
    2

/-- Twice the canonical propagation depth never exceeds the actual base-L1
distance. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1Depth_two_mul_le
    (H : ℕ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    2 *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1Depth
          H target source ≤
      periodicHypercubicEdgeBaseL1Distance
        (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H source) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1Depth
  omega

/-- Canonical geometric local-Green weight at target/source base-L1
separation. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1GreenWeight
    (H : ℕ)
    (beta : ℝ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  (18 *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
        beta) ^
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1Depth
        H target source /
    (1 -
      18 *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
          beta)

/-- The canonical local-Green weight is nonnegative below the strict local
threshold. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1GreenWeight_nonneg
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hThreshold :
      18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta <
        1)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1GreenWeight
        H beta target source := by
  let rho : ℝ :=
    18 *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
        beta
  have hEta :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
          beta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence_nonneg
      beta hbeta
  have hRho : 0 ≤ rho := by
    dsimp [rho]
    positivity
  have hRhoLt : rho < 1 := by
    simpa [rho] using hThreshold
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1GreenWeight
  exact
    div_nonneg
      (pow_nonneg hRho _)
      (le_of_lt (sub_pos.mpr hRhoLt))

/-- Every finite local-Harnack resolvent entry is bounded by its canonical
base-L1 Green weight. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackFiniteResolventEntry_le_baseL1GreenWeight
    (H M : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hThreshold :
      18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta <
        1)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackFiniteResolventEntry
        H beta hbeta M target source ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1GreenWeight
        H beta target source := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1GreenWeight
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackFiniteResolventEntry_le_geometric_of_two_mul_le_baseL1Distance
      H
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1Depth
        H target source)
      M beta hbeta hThreshold target source
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1Depth_two_mul_le
        H target source)

/-- A nonnegative forcing profile is propagated by the local finite Green
operator with its full sourcewise base-L1 weight retained. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackPartialResolvent_le_baseL1WeightedSum
    (H M : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hThreshold :
      18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta <
        1)
    (b : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hbNonneg : ∀ source, 0 ≤ b source)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    finiteNonnegativeKernelPartialResolvent
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
          H beta hbeta).influence
        b M target ≤
      ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1GreenWeight
            H beta target source *
          b source := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackPartialResolvent_eq_sum_finiteResolventEntry_mul]
  apply Finset.sum_le_sum
  intro source _hsource
  exact
    mul_le_mul_of_nonneg_right
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackFiniteResolventEntry_le_baseL1GreenWeight
        H M beta hbeta hThreshold target source)
      (hbNonneg source)

/-- The source-to-target remote perturbation after one local Green
propagation, retaining the intermediate-link base-L1 weight. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalGreenWeightedRemoteColumn
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  ∑ mid : PeriodicHypercubicEvenSpatialSliceLink H,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1GreenWeight
        H beta target mid *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
        H N hN beta hbeta A source mid

/-- The weighted remote column is nonnegative under the strict local
threshold. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalGreenWeightedRemoteColumn_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hThreshold :
      18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta <
        1)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalGreenWeightedRemoteColumn
        H N hN beta hbeta A target source := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalGreenWeightedRemoteColumn
  exact
    Finset.sum_nonneg fun mid _ =>
      mul_nonneg
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1GreenWeight_nonneg
          H beta hbeta hThreshold target mid)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual_nonneg
          H N hN beta hbeta A source mid)

/-- The local Green response to the explicit remote forcing is controlled by
the weighted remote convolution, without collapsing to a global L1 profile
mass. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackPartialResolvent_remoteForcing_le_weightedRemoteConvolution
    (H N M : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hThreshold :
      18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta <
        1)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (w : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hwNonneg : ∀ source, 0 ≤ w source)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    finiteNonnegativeKernelPartialResolvent
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
          H beta hbeta).influence
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationForcing
          H N hN beta hbeta A w)
        M target ≤
      ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalGreenWeightedRemoteColumn
            H N hN beta hbeta A target source *
          w source := by
  have hForcingNonneg :
      ∀ mid : PeriodicHypercubicEvenSpatialSliceLink H,
        0 ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationForcing
            H N hN beta hbeta A w mid := by
    intro mid
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationForcing_nonneg
        H N hN beta hbeta A w hwNonneg mid
  have hGreen :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackPartialResolvent_le_baseL1WeightedSum
      H M beta hbeta hThreshold
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationForcing
        H N hN beta hbeta A w)
      hForcingNonneg target
  refine hGreen.trans ?_
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationForcing
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationKernel
    finiteNonnegativeKernelApply
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalGreenWeightedRemoteColumn
  calc
    (∑ mid : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1GreenWeight
          H beta target mid *
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
              H N hN beta hbeta A source mid *
            w source)) =
      ∑ mid : PeriodicHypercubicEvenSpatialSliceLink H,
        ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1GreenWeight
              H beta target mid *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
              H N hN beta hbeta A source mid) *
            w source := by
      apply Finset.sum_congr rfl
      intro mid _hmid
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro source _hsource
      ring
    _ =
      ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
        ∑ mid : PeriodicHypercubicEvenSpatialSliceLink H,
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1GreenWeight
              H beta target mid *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
              H N hN beta hbeta A source mid) *
            w source := by
      rw [Finset.sum_comm]
    _ =
      ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
        (∑ mid : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1GreenWeight
              H beta target mid *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
              H N hN beta hbeta A source mid) *
          w source := by
      apply Finset.sum_congr rfl
      intro source _hsource
      rw [Finset.sum_mul]

/-- Singleton physical-envelope comparison with the remote contribution kept as
a spatially weighted remote convolution.

The direct local source term decays in target/source base-L1 distance, the
remote term retains its intermediate-link geometry, and only the finite local
power remainder remains unclosed. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeft_singleton_localGeometric_add_weightedRemoteConvolution_add_remainder
    (H N D M : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hThreshold :
      18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta <
        1)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (hDistance :
      2 * D ≤
        periodicHypercubicEdgeBaseL1Distance
          (PeriodicHypercubicEvenSideLength H)
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H source))
    (amplitude : ℝ)
    (hAmplitude : 0 ≤ amplitude)
    (w : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hwNonneg : ∀ t, 0 ≤ w t)
    (distanceBound : ℝ)
    (hDistanceBound : 0 ≤ distanceBound)
    (hwBound : ∀ t, w t ≤ distanceBound)
    (hComparison :
      ∀ t,
        w t ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackSingletonForcing
              source amplitude t +
            finiteNonnegativeKernelApply
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
                H N hN beta hbeta A).influence
              w t) :
    w target ≤
      ((18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta) ^ D /
        (1 -
          18 *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
              beta)) *
          amplitude +
        (∑ s : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalGreenWeightedRemoteColumn
              H N hN beta hbeta A target s *
            w s) +
        (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta) ^ M * distanceBound := by
  let localKernel :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
      H beta hbeta
  let remoteForcing :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationForcing
      H N hN beta hbeta A w
  let rho : ℝ :=
    18 *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
        beta
  have hBase :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeft_singleton_localGeometric_add_remoteResolvent_add_remainder
      H N D M hN beta hbeta hThreshold A source target hDistance
      amplitude hAmplitude w distanceBound hDistanceBound hwBound hComparison
  have hRemote :
      finiteNonnegativeKernelPartialResolvent
          localKernel.influence remoteForcing M target ≤
        ∑ s : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalGreenWeightedRemoteColumn
              H N hN beta hbeta A target s *
            w s := by
    simpa [localKernel, remoteForcing] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackPartialResolvent_remoteForcing_le_weightedRemoteConvolution
        H N M hN beta hbeta hThreshold A w hwNonneg target
  calc
    w target ≤
      (rho ^ D / (1 - rho)) * amplitude +
        finiteNonnegativeKernelPartialResolvent
          localKernel.influence remoteForcing M target +
        rho ^ M * distanceBound := by
      simpa [localKernel, remoteForcing, rho] using hBase
    _ ≤
      (rho ^ D / (1 - rho)) * amplitude +
        (∑ s : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalGreenWeightedRemoteColumn
              H N hN beta hbeta A target s *
            w s) +
        rho ^ M * distanceBound := by
      exact
        add_le_add
          (add_le_add
            (le_refl ((rho ^ D / (1 - rho)) * amplitude))
            hRemote)
          (le_refl (rho ^ M * distanceBound))
    _ =
      ((18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta) ^ D /
        (1 -
          18 *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
              beta)) *
          amplitude +
        (∑ s : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalGreenWeightedRemoteColumn
              H N hN beta hbeta A target s *
            w s) +
        (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta) ^ M * distanceBound := by
      rfl

end

end MathlibAnalytic
end MGAP4D
