import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferencePhysicalLeftLocalHarnackKernelBaseL1FiniteResolvent
import MGAP4D.MathlibAnalytic.FiniteNonnegativeKernelComparisonIteration
import Mathlib.Tactic

/-!
# Local-Harnack resolvent with explicit remote perturbation

The physical continuous-vacuum influence envelope is exactly the sum of the
intrinsic local Harnack kernel and the source-aligned remote physical residual.
This file records the finite comparison algebra needed to exploit that split
without assuming that the remote residual is already small.

The key step is to rewrite a comparison inequality

  w <= v + (K_local + R_remote) w

as

  w <= (v + R_remote w) + K_local w.

Only `K_local` is then iterated.  The remote term remains an explicit forcing
inside the finite local resolvent.  This avoids the circular move of assuming a
remote-residual decay estimate that itself depends on the covariance decay
still to be proved.

No infinite-resolvent, vanishing-remainder, ergodicity, covariance-decay, or
mass-gap statement is made here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance physicalLeftLocalHarnackRemotePerturbationSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Finite partial resolvents are additive in their forcing profile. -/
theorem finiteNonnegativeKernelPartialResolvent_add
    {ι : Type*}
    [Fintype ι]
    (kernel : ι → ι → ℝ)
    (b r : ι → ℝ)
    (n : ℕ)
    (target : ι) :
    finiteNonnegativeKernelPartialResolvent
        kernel (fun i => b i + r i) n target =
      finiteNonnegativeKernelPartialResolvent kernel b n target +
        finiteNonnegativeKernelPartialResolvent kernel r n target := by
  induction n generalizing target with
  | zero =>
      simp
  | succ n ih =>
      simp only [finiteNonnegativeKernelPartialResolvent_succ]
      have hPrevious :
          finiteNonnegativeKernelPartialResolvent
              kernel (fun i => b i + r i) n =
            fun i =>
              finiteNonnegativeKernelPartialResolvent kernel b n i +
                finiteNonnegativeKernelPartialResolvent kernel r n i := by
        funext i
        exact ih i
      rw [hPrevious]
      rw [finiteNonnegativeKernelApply_add]
      ring

/-- The remote part in the orientation used by finite kernel application.
The source-aligned residual is stored as `residual source target`, whereas a
comparison kernel is applied as `kernel target source`. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationKernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
    H N hN beta hbeta A source target

/-- The remote perturbation kernel is pointwise nonnegative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationKernel_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationKernel
        H N hN beta hbeta A target source := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual_nonneg
      H N hN beta hbeta A source target

/-- Pointwise, the physical envelope is exactly the local Harnack kernel plus
the correctly oriented remote perturbation kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_eq_localHarnack_add_remotePerturbationKernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
        H N hN beta hbeta A).influence target source =
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
          H beta hbeta).influence target source +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationKernel
          H N hN beta hbeta A target source := by
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationKernel] using
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_eq_localHarnack_add_remoteResidual
      H N hN beta hbeta A target source

/-- Kernel application of the physical envelope splits exactly into local and
remote applications. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_apply_eq_localHarnack_add_remotePerturbation
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (w : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    finiteNonnegativeKernelApply
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
          H N hN beta hbeta A).influence
        w target =
      finiteNonnegativeKernelApply
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
            H beta hbeta).influence
          w target +
        finiteNonnegativeKernelApply
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationKernel
            H N hN beta hbeta A)
          w target := by
  classical
  unfold finiteNonnegativeKernelApply
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro source _hsource
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_eq_localHarnack_add_remotePerturbationKernel]
  ring

/-- The current remote contribution generated by a profile `w`, before any
smallness estimate is imposed. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationForcing
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (w : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  finiteNonnegativeKernelApply
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationKernel
      H N hN beta hbeta A)
    w target

/-- A nonnegative profile produces a nonnegative remote forcing. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationForcing_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (w : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hw : ∀ source, 0 ≤ w source)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationForcing
        H N hN beta hbeta A w target := by
  exact
    finiteNonnegativeKernelApply_nonneg
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationKernel
        H N hN beta hbeta A)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationKernel_nonneg
        H N hN beta hbeta A)
      w hw target

/-- Finite local-resolvent perturbation formula.

A profile controlled by the full physical envelope is bounded by the finite
local Harnack resolvent of the original forcing, plus the finite local Harnack
resolvent of the explicit remote forcing, plus the unclosed degree-`M` local
remainder.  No smallness assumption on the remote term is used. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeft_localHarnackRemotePerturbation_iterate
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (v w : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hComparison :
      ∀ target,
        w target ≤
          v target +
            finiteNonnegativeKernelApply
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
                H N hN beta hbeta A).influence
              w target)
    (M : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    w target ≤
      finiteNonnegativeKernelPartialResolvent
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
            H beta hbeta).influence
          v M target +
        finiteNonnegativeKernelPartialResolvent
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
            H beta hbeta).influence
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationForcing
            H N hN beta hbeta A w)
          M target +
        finiteNonnegativeKernelPowerApply
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
            H beta hbeta).influence
          w M target := by
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
      H beta hbeta
  let remoteForcing :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationForcing
      H N hN beta hbeta A w
  have hLocalComparison :
      ∀ target,
        w target ≤
          (v target + remoteForcing target) +
            finiteNonnegativeKernelApply K.influence w target := by
    intro t
    have h := hComparison t
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_apply_eq_localHarnack_add_remotePerturbation]
      at h
    simpa [K, remoteForcing,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationForcing,
      add_assoc, add_left_comm, add_comm] using h
  have hIter :=
    finiteNonnegativeKernelComparison_iterate
      K.influence K.influence_nonneg
      (fun t => v t + remoteForcing t)
      w hLocalComparison M target
  rw [finiteNonnegativeKernelPartialResolvent_add] at hIter
  simpa [K, remoteForcing] using hIter

/-- The same perturbation formula with the remaining local degree-`M` term
reduced to the explicit row-mass factor
`rho_local(beta)^M * distanceBound`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeft_localHarnackRemotePerturbation_iterate_le_geometricResidual
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (v w : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (distanceBound : ℝ)
    (hDistanceBound : 0 ≤ distanceBound)
    (hwBound : ∀ target, w target ≤ distanceBound)
    (hComparison :
      ∀ target,
        w target ≤
          v target +
            finiteNonnegativeKernelApply
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
                H N hN beta hbeta A).influence
              w target)
    (M : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    w target ≤
      finiteNonnegativeKernelPartialResolvent
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
            H beta hbeta).influence
          v M target +
        finiteNonnegativeKernelPartialResolvent
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
            H beta hbeta).influence
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationForcing
            H N hN beta hbeta A w)
          M target +
        (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta) ^ M * distanceBound := by
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
      H beta hbeta
  let rho : ℝ :=
    18 *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
        beta
  let remoteForcing :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationForcing
      H N hN beta hbeta A w
  have hEta :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
          beta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence_nonneg
      beta hbeta
  have hRho : 0 ≤ rho := by
    dsimp [rho]
    positivity
  have hRow :
      ∀ t : PeriodicHypercubicEvenSpatialSliceLink H,
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          K.influence t source) ≤ rho := by
    intro t
    simpa [K, rho, finiteInfluenceKernelRowSum] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel_rowSum_le_eighteen_mul
        H beta hbeta t
  have hLocalComparison :
      ∀ t,
        w t ≤
          (v t + remoteForcing t) +
            finiteNonnegativeKernelApply K.influence w t := by
    intro t
    have h := hComparison t
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_apply_eq_localHarnack_add_remotePerturbation]
      at h
    simpa [K, remoteForcing,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationForcing,
      add_assoc, add_left_comm, add_comm] using h
  have hIter :=
    finiteNonnegativeKernelComparison_iterate_le_partial_add_geometricResidual
      K.influence K.influence_nonneg rho hRho hRow
      (fun t => v t + remoteForcing t)
      w distanceBound hDistanceBound hwBound hLocalComparison M target
  rw [finiteNonnegativeKernelPartialResolvent_add] at hIter
  simpa [K, rho, remoteForcing] using hIter

end

end MathlibAnalytic
end MGAP4D
