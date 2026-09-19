import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferencePhysicalLeftLocalHarnackRemotePerturbation
import Mathlib.Tactic

/-!
# Singleton source through the local-Harnack remote-perturbation resolvent

The local-Harnack finite resolvent and the local-plus-remote perturbation
identity are now both available.  This file connects them at the source-local
forcing relevant to the terminal covariance route.

First, the generic finite partial resolvent is identified with the finite sum
of kernel powers.  For a singleton forcing, the generic powers are then
identified with the recursive local-Harnack kernel entries already carrying
base-L1 finite propagation.  Consequently the direct local contribution is
bounded by the explicit geometric factor from the preceding base-L1 theorem.

The final statement leaves two terms explicit:

* the local resolvent applied to the remote physical forcing;
* the finite degree-M local remainder.

Thus the direct source-local part has spatial decay without assuming any
remote-residual decay and without closing the covariance remainder.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance physicalLeftLocalHarnackSingletonRemoteResolventSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- A finite kernel action commutes with a finite sum of profiles. -/
theorem finiteNonnegativeKernelApply_sum_range
    {ι : Type}
    [Fintype ι]
    (kernel : ι → ι → ℝ)
    (f : ℕ → ι → ℝ)
    (n : ℕ)
    (target : ι) :
    finiteNonnegativeKernelApply
        kernel
        (fun source => ∑ k ∈ Finset.range n, f k source)
        target =
      ∑ k ∈ Finset.range n,
        finiteNonnegativeKernelApply kernel (f k) target := by
  induction n with
  | zero =>
      simp [finiteNonnegativeKernelApply]
  | succ n ih =>
      have hProfile :
          (fun source : ι => ∑ k ∈ Finset.range (n + 1), f k source) =
            fun source =>
              (∑ k ∈ Finset.range n, f k source) + f n source := by
        funext source
        rw [Finset.sum_range_succ]
      rw [hProfile, finiteNonnegativeKernelApply_add, ih, Finset.sum_range_succ]

/-- The degree-zero kernel power followed by all shifted powers is exactly the
next finite power prefix. -/
theorem finiteNonnegativeKernelPowerApply_zero_add_sum_succ
    {ι : Type}
    [Fintype ι]
    (kernel : ι → ι → ℝ)
    (b : ι → ℝ)
    (n : ℕ)
    (target : ι) :
    b target +
        (∑ k ∈ Finset.range n,
          finiteNonnegativeKernelPowerApply kernel b (k + 1) target) =
      ∑ k ∈ Finset.range (n + 1),
        finiteNonnegativeKernelPowerApply kernel b k target := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      rw [← add_assoc, ih]

/-- The recursive finite partial resolvent is the finite sum of kernel powers. -/
theorem finiteNonnegativeKernelPartialResolvent_eq_sum_powerApply_explicit
    {ι : Type}
    [Fintype ι]
    (kernel : ι → ι → ℝ)
    (b : ι → ℝ)
    (n : ℕ)
    (target : ι) :
    finiteNonnegativeKernelPartialResolvent kernel b n target =
      ∑ k ∈ Finset.range n,
        finiteNonnegativeKernelPowerApply kernel b k target := by
  induction n generalizing target with
  | zero =>
      simp
  | succ n ih =>
      simp only [finiteNonnegativeKernelPartialResolvent_succ]
      have hPrevious :
          finiteNonnegativeKernelPartialResolvent kernel b n =
            fun source =>
              ∑ k ∈ Finset.range n,
                finiteNonnegativeKernelPowerApply kernel b k source := by
        funext source
        exact ih source
      rw [hPrevious]
      rw [finiteNonnegativeKernelApply_sum_range]
      have hShift :
          (∑ k ∈ Finset.range n,
            finiteNonnegativeKernelApply
              kernel
              (finiteNonnegativeKernelPowerApply kernel b k)
              target) =
            ∑ k ∈ Finset.range n,
              finiteNonnegativeKernelPowerApply kernel b (k + 1) target := by
        apply Finset.sum_congr rfl
        intro k _hk
        rfl
      rw [hShift]
      exact
        finiteNonnegativeKernelPowerApply_zero_add_sum_succ
          kernel b n target

/-- A source-local forcing profile on the physical spatial-link set. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackSingletonForcing
    {H : ℕ}
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (amplitude : ℝ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  if target = source then amplitude else 0

/-- A generic power of the actual local Harnack kernel acting on singleton
forcing is exactly the recursive local-Harnack kernel entry times the source
amplitude. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackPowerApply_singleton_eq_iterate_mul
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (amplitude : ℝ) :
    ∀ d : ℕ,
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        finiteNonnegativeKernelPowerApply
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
              H beta hbeta).influence
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackSingletonForcing
              source amplitude)
            d target =
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel
              H beta hbeta d target source *
            amplitude := by
  intro d
  induction d with
  | zero =>
      intro target
      by_cases hEq : target = source
      · simp [
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackSingletonForcing,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel,
          hEq]
      · simp [
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackSingletonForcing,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel,
          hEq]
  | succ d ih =>
      intro target
      let K :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
          H beta hbeta
      change
        (∑ mid : PeriodicHypercubicEvenSpatialSliceLink H,
          K.influence target mid *
            finiteNonnegativeKernelPowerApply
              K.influence
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackSingletonForcing
                source amplitude)
              d mid) =
          (∑ mid : PeriodicHypercubicEvenSpatialSliceLink H,
            K.influence target mid *
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel
                H beta hbeta d mid source) *
            amplitude
      calc
        (∑ mid : PeriodicHypercubicEvenSpatialSliceLink H,
          K.influence target mid *
            finiteNonnegativeKernelPowerApply
              K.influence
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackSingletonForcing
                source amplitude)
              d mid) =
            ∑ mid : PeriodicHypercubicEvenSpatialSliceLink H,
              (K.influence target mid *
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel
                  H beta hbeta d mid source) * amplitude := by
          apply Finset.sum_congr rfl
          intro mid _hmid
          rw [ih mid]
          ring
        _ =
            (∑ mid : PeriodicHypercubicEvenSpatialSliceLink H,
              K.influence target mid *
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel
                  H beta hbeta d mid source) * amplitude := by
          rw [Finset.sum_mul]

/-- The generic finite local partial resolvent of singleton forcing is exactly
the local-Harnack finite-resolvent entry times the amplitude. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackPartialResolvent_singleton_eq_finiteResolventEntry_mul
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (M : ℕ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (amplitude : ℝ) :
    finiteNonnegativeKernelPartialResolvent
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
          H beta hbeta).influence
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackSingletonForcing
          source amplitude)
        M target =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackFiniteResolventEntry
          H beta hbeta M target source *
        amplitude := by
  rw [finiteNonnegativeKernelPartialResolvent_eq_sum_powerApply_explicit]
  calc
    (∑ d ∈ Finset.range M,
      finiteNonnegativeKernelPowerApply
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
          H beta hbeta).influence
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackSingletonForcing
          source amplitude)
        d target) =
        ∑ d ∈ Finset.range M,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel
              H beta hbeta d target source *
            amplitude := by
      apply Finset.sum_congr rfl
      intro d _hd
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackPowerApply_singleton_eq_iterate_mul
          H beta hbeta source amplitude d target
    _ =
        (∑ d ∈ Finset.range M,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackIterateKernel
            H beta hbeta d target source) * amplitude := by
      rw [Finset.sum_mul]
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackFiniteResolventEntry
          H beta hbeta M target source *
        amplitude := by
      rfl

/-- Under the strict local Harnack threshold, singleton forcing inherits the
base-L1 geometric finite-resolvent bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackPartialResolvent_singleton_le_geometric_of_two_mul_le_baseL1Distance
    (H D M : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hThreshold :
      18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta <
        1)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hDistance :
      2 * D ≤
        periodicHypercubicEdgeBaseL1Distance
          (PeriodicHypercubicEvenSideLength H)
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H source))
    (amplitude : ℝ)
    (hAmplitude : 0 ≤ amplitude) :
    finiteNonnegativeKernelPartialResolvent
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
          H beta hbeta).influence
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackSingletonForcing
          source amplitude)
        M target ≤
      ((18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta) ^ D /
        (1 -
          18 *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
              beta)) *
        amplitude := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackPartialResolvent_singleton_eq_finiteResolventEntry_mul]
  exact
    mul_le_mul_of_nonneg_right
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackFiniteResolventEntry_le_geometric_of_two_mul_le_baseL1Distance
        H D M beta hbeta hThreshold target source hDistance)
      hAmplitude

/-- The direct source-local contribution of a full physical-envelope comparison
has explicit base-L1 geometric decay.  What remains is precisely the local
resolvent of the remote physical forcing plus the finite local power remainder.

No estimate on the remote forcing is assumed here. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeft_singleton_localGeometric_add_remoteResolvent_add_remainder
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
        finiteNonnegativeKernelPartialResolvent
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
            H beta hbeta).influence
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationForcing
            H N hN beta hbeta A w)
          M target +
        (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta) ^ M * distanceBound := by
  let singleton :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackSingletonForcing
      source amplitude
  let remoteForcing :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationForcing
      H N hN beta hbeta A w
  let localKernel :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
      H beta hbeta
  let rho : ℝ :=
    18 *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
        beta
  have hPerturb :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeft_localHarnackRemotePerturbation_iterate_le_geometricResidual
      H N hN beta hbeta A singleton w
      distanceBound hDistanceBound hwBound
      (by simpa [singleton] using hComparison)
      M target
  have hLocal :
      finiteNonnegativeKernelPartialResolvent
          localKernel.influence singleton M target ≤
        (rho ^ D / (1 - rho)) * amplitude := by
    simpa [localKernel, singleton, rho] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackPartialResolvent_singleton_le_geometric_of_two_mul_le_baseL1Distance
        H D M beta hbeta hThreshold target source hDistance amplitude hAmplitude
  calc
    w target ≤
        finiteNonnegativeKernelPartialResolvent
            localKernel.influence singleton M target +
          finiteNonnegativeKernelPartialResolvent
            localKernel.influence remoteForcing M target +
          rho ^ M * distanceBound := by
      simpa [localKernel, singleton, remoteForcing, rho] using hPerturb
    _ ≤
        (rho ^ D / (1 - rho)) * amplitude +
          finiteNonnegativeKernelPartialResolvent
            localKernel.influence remoteForcing M target +
          rho ^ M * distanceBound := by
      exact
        add_le_add
          (add_le_add hLocal
            (le_refl
              (finiteNonnegativeKernelPartialResolvent
                localKernel.influence remoteForcing M target)))
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
        finiteNonnegativeKernelPartialResolvent
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
            H beta hbeta).influence
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationForcing
            H N hN beta hbeta A w)
          M target +
        (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta) ^ M * distanceBound := by
      rfl

end

end MathlibAnalytic
end MGAP4D
