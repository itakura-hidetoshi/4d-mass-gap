import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumRemoteKernelSectionOneLinkCovarianceDirichlet
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceDistinctFiberDeterministicScheduleTransport
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory

noncomputable section

local instance remoteKernelSectionDeterministicScheduleCovarianceTelescopeSpecialUnitaryMeasurableSpace
    (N : Nat) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) Complex) :=
  specialUnitaryGroupMeasurableSpace N

local instance remoteKernelSectionDeterministicScheduleCovarianceTelescopeSpatialLinkFintype
    (H : Nat) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance remoteKernelSectionDeterministicScheduleCovarianceTelescopeKernelSectionProbabilityMeasure
    (H N : Nat)
    (hN : 0 < N)
    (beta : Real)
    (hbeta : 0 <= beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta C) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_isProbabilityMeasure
    H N hN beta hbeta C

/-- The actual remote one-link projection is definitionally the head action of
the existing literal deterministic schedule on the tail schedule observable.
This is the bridge from the L2 covariance layer to the pre-existing
deterministic-schedule variation carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_schedule_eq_schedule_cons
    (H N : Nat)
    (hN : 0 < N)
    (beta : Real)
    (hbeta : 0 <= beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (fibers : List (PeriodicHypercubicEvenSpatialSliceLink H))
    (k g2 : Matrix.specialUnitaryGroup (Fin N) Complex)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N -> Real) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
        H N hN beta hbeta B target source fiber k g2
        (fun A =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
            H N hN beta hbeta B target source g2 fibers k A F) =
      (fun A =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
          H N hN beta hbeta B target source g2 (fiber :: fibers) k A F) := by
  rfl

/-- Every finite literal deterministic schedule preserves L2 under the actual
remote fixed-right kernel-section law.  The proof iterates the already-proved
actual one-link L2 conditional projection carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionDeterministicScheduleExpectation_memLp_two
    (H N : Nat)
    (hN : 0 < N)
    (beta : Real)
    (hbeta : 0 <= beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hne : target ≠ source)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source)
    (fibers : List (PeriodicHypercubicEvenSpatialSliceLink H))
    (k g2 : Matrix.specialUnitaryGroup (Fin N) Complex)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N -> Real)
    (hF : MemLp F 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source k) target g2))) :
    MemLp
      (fun A =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
          H N hN beta hbeta B target source g2 fibers k A F)
      2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source k) target g2)) := by
  induction fibers with
  | nil =>
      simpa using hF
  | cons fiber fibers ih =>
      have hProjection :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_memLp_two
          H N hN beta hbeta B hne hNoShare fiber k g2
          (fun A =>
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
              H N hN beta hbeta B target source g2 fibers k A F)
          ih
      simpa only [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_schedule_eq_schedule_cons] using
        hProjection

/-- Recursive sum of the exact one-link covariance losses along the existing
ordered deterministic schedule.  At a head fiber, the tail observable has
already been formed, exactly matching the schedule convention. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionDeterministicScheduleCovarianceDirichletSum
    (H N : Nat)
    (hN : 0 < N)
    (beta : Real)
    (hbeta : 0 <= beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g2 : Matrix.specialUnitaryGroup (Fin N) Complex)
    (f g : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N -> Real) :
    List (PeriodicHypercubicEvenSpatialSliceLink H) -> Real
  | [] => 0
  | fiber :: fibers =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionDeterministicScheduleCovarianceDirichletSum
          H N hN beta hbeta B target source k g2 f g fibers +
        realIntegralCovariance
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta
            (Function.update (Function.update B source k) target g2))
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
            H N hN beta hbeta B target source fiber k g2 f)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
            H N hN beta hbeta B target source fiber k g2
            (fun A =>
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
                H N hN beta hbeta B target source g2 fibers k A g))

/-- Exact covariance telescope along an arbitrary finite ordered literal
continuous-C5 deterministic schedule.  It is an identity, not a decay bound:
the covariance lost after the schedule is exactly the sum of the one-link
fluctuation covariance pairings encountered along the tail-observable
recursion. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionDeterministicSchedule_realIntegralCovariance_telescope_of_memLp_two
    (H N : Nat)
    (hN : 0 < N)
    (beta : Real)
    (hbeta : 0 <= beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hne : target ≠ source)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source)
    (fibers : List (PeriodicHypercubicEvenSpatialSliceLink H))
    (k g2 : Matrix.specialUnitaryGroup (Fin N) Complex)
    (f g : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N -> Real)
    (hf : MemLp f 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source k) target g2)))
    (hg : MemLp g 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source k) target g2))) :
    realIntegralCovariance
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta
          (Function.update (Function.update B source k) target g2))
        f g -
      realIntegralCovariance
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta
          (Function.update (Function.update B source k) target g2))
        f
        (fun A =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
            H N hN beta hbeta B target source g2 fibers k A g) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionDeterministicScheduleCovarianceDirichletSum
        H N hN beta hbeta B target source k g2 f g fibers := by
  let mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta
      (Function.update (Function.update B source k) target g2)
  change
    realIntegralCovariance mu f g -
      realIntegralCovariance mu f
        (fun A =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
            H N hN beta hbeta B target source g2 fibers k A g) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionDeterministicScheduleCovarianceDirichletSum
        H N hN beta hbeta B target source k g2 f g fibers
  induction fibers with
  | nil =>
      simp [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionDeterministicScheduleCovarianceDirichletSum]
  | cons fiber fibers ih =>
      let G : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N -> Real :=
        fun A =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
            H N hN beta hbeta B target source g2 fibers k A g
      have hG :
          MemLp G 2 mu := by
        dsimp [G, mu]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionDeterministicScheduleExpectation_memLp_two
            H N hN beta hbeta B hne hNoShare fibers k g2 g hg
      have hDirichlet :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLink_realIntegralCovariance_sub_projection_eq_fluctuation_pairing_of_memLp_two
          H N hN beta hbeta B hne hNoShare fiber k g2 f G hf hG
      have hBridge :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_schedule_eq_schedule_cons
          H N hN beta hbeta B target source fiber fibers k g2 g
      change
        realIntegralCovariance mu f g -
          realIntegralCovariance mu f
            (fun A =>
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
                H N hN beta hbeta B target source g2 (fiber :: fibers) k A g) =
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionDeterministicScheduleCovarianceDirichletSum
            H N hN beta hbeta B target source k g2 f g (fiber :: fibers)
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionDeterministicScheduleCovarianceDirichletSum]
      rw [← hBridge]
      change
        realIntegralCovariance mu f g -
          realIntegralCovariance mu f
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
              H N hN beta hbeta B target source fiber k g2 G) =
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionDeterministicScheduleCovarianceDirichletSum
              H N hN beta hbeta B target source k g2 f g fibers +
            realIntegralCovariance mu
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
                H N hN beta hbeta B target source fiber k g2 f)
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
                H N hN beta hbeta B target source fiber k g2 G)
      change
        realIntegralCovariance mu f G -
          realIntegralCovariance mu f
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
              H N hN beta hbeta B target source fiber k g2 G) =
          realIntegralCovariance mu
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
              H N hN beta hbeta B target source fiber k g2 f)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
              H N hN beta hbeta B target source fiber k g2 G) at hDirichlet
      linarith

end

end MathlibAnalytic
end MGAP4D
