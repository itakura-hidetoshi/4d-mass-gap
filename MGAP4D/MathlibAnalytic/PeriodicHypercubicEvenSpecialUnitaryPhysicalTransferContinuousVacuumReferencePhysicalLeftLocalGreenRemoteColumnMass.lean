import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferencePhysicalLeftLocalHarnackSingletonRemoteResolvent
import Mathlib.Tactic

/-!
# Local Green control of remote physical forcing by column mass

The direct singleton contribution is now controlled by base-L1 geometric
decay, while the remaining remote term appears as the finite local-Harnack
resolvent applied to an explicit physical remote forcing.

This file reduces that local Green response to an L1 mass of the remote
forcing.  The remote forcing mass is then identified exactly with the
source-weighted sum of the source-aligned remote residual columns.

No uniform remote-residual certificate is assumed in the basic identities.
A final theorem allows any independently supplied column bound to be inserted,
making the remaining global-L1 obstruction explicit rather than hiding it.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance physicalLeftLocalGreenRemoteColumnMassSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Under the strict local Harnack threshold, the finite local partial
resolvent of any nonnegative forcing is bounded by the full local geometric
mass times the total L1 forcing mass. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackPartialResolvent_le_invGap_mul_sum
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
      (1 /
        (1 -
          18 *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
              beta)) *
        ∑ source : PeriodicHypercubicEvenSpatialSliceLink H, b source := by
  classical
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
      H beta hbeta
  let rho : ℝ :=
    18 *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
        beta
  let total : ℝ :=
    ∑ source : PeriodicHypercubicEvenSpatialSliceLink H, b source
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
  have hRow :
      ∀ t : PeriodicHypercubicEvenSpatialSliceLink H,
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          K.influence t source) ≤ rho := by
    intro t
    simpa [K, rho, finiteInfluenceKernelRowSum] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel_rowSum_le_eighteen_mul
        H beta hbeta t
  have hTotalNonneg : 0 ≤ total := by
    dsimp [total]
    exact Finset.sum_nonneg fun source _ => hbNonneg source
  have hbLeTotal :
      ∀ source : PeriodicHypercubicEvenSpatialSliceLink H,
        b source ≤ total := by
    intro source
    dsimp [total]
    exact
      Finset.single_le_sum
        (fun other _ => hbNonneg other)
        (Finset.mem_univ source)
  rw [finiteNonnegativeKernelPartialResolvent_eq_sum_powerApply_explicit]
  calc
    (∑ d ∈ Finset.range M,
      finiteNonnegativeKernelPowerApply K.influence b d target) ≤
        ∑ d ∈ Finset.range M, rho ^ d * total := by
      apply Finset.sum_le_sum
      intro d _hd
      exact
        finiteNonnegativeKernelPowerApply_le_coefficient_pow_mul
          K.influence K.influence_nonneg rho hRho hRow
          b total hTotalNonneg hbLeTotal d target
    _ =
        (∑ d ∈ Finset.range M, rho ^ d) * total := by
      rw [Finset.sum_mul]
    _ ≤
        (1 / (1 - rho)) * total := by
      exact
        mul_le_mul_of_nonneg_right
          (FiniteDistanceShellGeometricSum.sum_range_pow_le_one_div_one_sub
            rho hRho hRhoLt M)
          hTotalNonneg
    _ =
      (1 /
        (1 -
          18 *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
              beta)) *
        ∑ source : PeriodicHypercubicEvenSpatialSliceLink H, b source := by
      rfl

/-- The total remote forcing mass is exactly the profile-weighted sum of the
source-aligned remote residual column masses. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationForcing_sum_eq_weighted_remoteResidualColumns
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (w : PeriodicHypercubicEvenSpatialSliceLink H → ℝ) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationForcing
        H N hN beta hbeta A w target) =
      ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
        (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
            H N hN beta hbeta A source target) *
          w source := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationForcing
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationKernel
    finiteNonnegativeKernelApply
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro source _hsource
  rw [Finset.sum_mul]

/-- The local Green response to the explicit remote forcing is bounded by the
local geometric mass times the exact weighted remote-column mass. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackPartialResolvent_remoteForcing_le_weighted_remoteResidualColumns
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
      (1 /
        (1 -
          18 *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
              beta)) *
        ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          (∑ t : PeriodicHypercubicEvenSpatialSliceLink H,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
              H N hN beta hbeta A source t) *
            w source := by
  have hForcingNonneg :
      ∀ t : PeriodicHypercubicEvenSpatialSliceLink H,
        0 ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationForcing
            H N hN beta hbeta A w t := by
    intro t
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationForcing_nonneg
        H N hN beta hbeta A w hwNonneg t
  have hGreen :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackPartialResolvent_le_invGap_mul_sum
      H M beta hbeta hThreshold
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationForcing
        H N hN beta hbeta A w)
      hForcingNonneg target
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationForcing_sum_eq_weighted_remoteResidualColumns]
    at hGreen
  exact hGreen

/-- Any independently supplied uniform bound on every source-aligned remote
residual column bounds the weighted remote forcing mass by that scalar times
the total profile mass. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReference_weighted_remoteResidualColumns_le_bound_mul_sum
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (remoteBound : ℝ)
    (hColumn :
      ∀ source : PeriodicHypercubicEvenSpatialSliceLink H,
        (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
            H N hN beta hbeta A source target) ≤ remoteBound)
    (w : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hwNonneg : ∀ source, 0 ≤ w source) :
    (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
          H N hN beta hbeta A source target) *
        w source) ≤
      remoteBound *
        ∑ source : PeriodicHypercubicEvenSpatialSliceLink H, w source := by
  calc
    (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
          H N hN beta hbeta A source target) *
        w source) ≤
        ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          remoteBound * w source := by
      apply Finset.sum_le_sum
      intro source _hsource
      exact
        mul_le_mul_of_nonneg_right
          (hColumn source)
          (hwNonneg source)
    _ =
      remoteBound *
        ∑ source : PeriodicHypercubicEvenSpatialSliceLink H, w source := by
      rw [Finset.mul_sum]

/-- Combining the preceding two reductions: a remote-column bound controls the
local Green response to the remote forcing by the local inverse-gap factor
times that column bound and the total profile mass. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackPartialResolvent_remoteForcing_le_invGap_mul_remoteBound_mul_sum
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
    (remoteBound : ℝ)
    (hColumn :
      ∀ source : PeriodicHypercubicEvenSpatialSliceLink H,
        (∑ t : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
            H N hN beta hbeta A source t) ≤ remoteBound)
    (w : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hwNonneg : ∀ source, 0 ≤ w source)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    finiteNonnegativeKernelPartialResolvent
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
          H beta hbeta).influence
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationForcing
          H N hN beta hbeta A w)
        M target ≤
      (1 /
        (1 -
          18 *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
              beta)) *
        (remoteBound *
          ∑ source : PeriodicHypercubicEvenSpatialSliceLink H, w source) := by
  let rho : ℝ :=
    18 *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
        beta
  have hRhoLt : rho < 1 := by
    simpa [rho] using hThreshold
  have hInvNonneg : 0 ≤ 1 / (1 - rho) := by
    exact div_nonneg (by norm_num) (le_of_lt (sub_pos.mpr hRhoLt))
  have hGreen :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackPartialResolvent_remoteForcing_le_weighted_remoteResidualColumns
      H N M hN beta hbeta hThreshold A w hwNonneg target
  have hColumns :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReference_weighted_remoteResidualColumns_le_bound_mul_sum
      H N hN beta hbeta A remoteBound hColumn w hwNonneg
  exact hGreen.trans
    (by
      simpa [rho] using
        mul_le_mul_of_nonneg_left hColumns hInvNonneg)

/-- The singleton local-geometric perturbation estimate with an explicit
remote-column bound.  The only remaining global quantity from the remote
perturbation is the total mass of the comparison profile. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeft_singleton_localGeometric_add_remoteColumnMass_add_remainder
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
    (remoteBound : ℝ)
    (hColumn :
      ∀ s : PeriodicHypercubicEvenSpatialSliceLink H,
        (∑ t : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
            H N hN beta hbeta A s t) ≤ remoteBound)
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
        (1 /
          (1 -
            18 *
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
                beta)) *
          (remoteBound *
            ∑ s : PeriodicHypercubicEvenSpatialSliceLink H, w s) +
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
        (1 / (1 - rho)) *
          (remoteBound *
            ∑ s : PeriodicHypercubicEvenSpatialSliceLink H, w s) := by
    simpa [localKernel, remoteForcing, rho] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackPartialResolvent_remoteForcing_le_invGap_mul_remoteBound_mul_sum
        H N M hN beta hbeta hThreshold A remoteBound hColumn w hwNonneg target
  calc
    w target ≤
      (rho ^ D / (1 - rho)) * amplitude +
        finiteNonnegativeKernelPartialResolvent
          localKernel.influence remoteForcing M target +
        rho ^ M * distanceBound := by
      simpa [localKernel, remoteForcing, rho] using hBase
    _ ≤
      (rho ^ D / (1 - rho)) * amplitude +
        (1 / (1 - rho)) *
          (remoteBound *
            ∑ s : PeriodicHypercubicEvenSpatialSliceLink H, w s) +
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
        (1 /
          (1 -
            18 *
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
                beta)) *
          (remoteBound *
            ∑ s : PeriodicHypercubicEvenSpatialSliceLink H, w s) +
        (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta) ^ M * distanceBound := by
      rfl

end

end MathlibAnalytic
end MGAP4D
