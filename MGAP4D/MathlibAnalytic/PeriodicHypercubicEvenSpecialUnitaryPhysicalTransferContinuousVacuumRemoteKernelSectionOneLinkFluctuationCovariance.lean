import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumRemoteKernelSectionOneLinkProjectionL2
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumRemoteKernelSectionOneLinkCovarianceSelfAdjoint
import MGAP4D.MathlibAnalytic.RealIntegralCovarianceLinearity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory

noncomputable section

local instance remoteKernelSectionOneLinkFluctuationCovarianceSpecialUnitaryMeasurableSpace
    (N : Nat) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) Complex) :=
  specialUnitaryGroupMeasurableSpace N

local instance remoteKernelSectionOneLinkFluctuationCovarianceSpatialLinkFintype
    (H : Nat) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance remoteKernelSectionOneLinkFluctuationCovarianceKernelSectionProbabilityMeasure
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

/-- The actual one-link fluctuation Q = I - P is self-adjoint for ordinary
real covariance on square-integrable observables under the remote kernel-section
law.  This is an algebraic consequence of covariance subtraction and
self-adjointness of the actual conditional projection P. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation_realIntegralCovariance_symm_of_memLp_two
    (H N : Nat)
    (hN : 0 < N)
    (beta : Real)
    (hbeta : 0 <= beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hne : target ≠ source)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source)
    (fiber : PeriodicHypercubicEvenSpatialSliceLink H)
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
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
          H N hN beta hbeta B target source fiber k g2 f)
        g =
      realIntegralCovariance
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta
          (Function.update (Function.update B source k) target g2))
        f
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
          H N hN beta hbeta B target source fiber k g2 g) := by
  let mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta
      (Function.update (Function.update B source k) target g2)
  have hPf :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_memLp_two
      H N hN beta hbeta B hne hNoShare fiber k g2 f hf
  have hPg :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_memLp_two
      H N hN beta hbeta B hne hNoShare fiber k g2 g hg
  have hLeft :
      realIntegralCovariance mu
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
            H N hN beta hbeta B target source fiber k g2 f)
          g =
        realIntegralCovariance mu f g -
          realIntegralCovariance mu
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
              H N hN beta hbeta B target source fiber k g2 f)
            g := by
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation] using
      realIntegralCovariance_sub_left_of_memLp_two
        mu
        f
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
          H N hN beta hbeta B target source fiber k g2 f)
        g hf hPf hg
  have hRight :
      realIntegralCovariance mu f
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
            H N hN beta hbeta B target source fiber k g2 g) =
        realIntegralCovariance mu f g -
          realIntegralCovariance mu f
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
              H N hN beta hbeta B target source fiber k g2 g) := by
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation] using
      realIntegralCovariance_sub_right_of_memLp_two
        mu
        g
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
          H N hN beta hbeta B target source fiber k g2 g)
        f hg hPg hf
  have hProjectionSymm :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_realIntegralCovariance_symm_of_memLp_two
      H N hN beta hbeta B hne hNoShare fiber k g2 f g hf hg
  change
    realIntegralCovariance mu
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
          H N hN beta hbeta B target source fiber k g2 f)
        g =
      realIntegralCovariance mu f
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
          H N hN beta hbeta B target source fiber k g2 g)
  calc
    realIntegralCovariance mu
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
          H N hN beta hbeta B target source fiber k g2 f)
        g =
      realIntegralCovariance mu f g -
        realIntegralCovariance mu
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
            H N hN beta hbeta B target source fiber k g2 f)
          g := hLeft
    _ = realIntegralCovariance mu f g -
        realIntegralCovariance mu f
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
            H N hN beta hbeta B target source fiber k g2 g) := by
      rw [hProjectionSymm]
    _ = realIntegralCovariance mu f
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
          H N hN beta hbeta B target source fiber k g2 g) := hRight.symm

/-- Exact left-slot covariance decomposition f = P f + Q f for the actual
remote kernel-section one-link projection and fluctuation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_add_fluctuation_realIntegralCovariance_left_of_memLp_two
    (H N : Nat)
    (hN : 0 < N)
    (beta : Real)
    (hbeta : 0 <= beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hne : target ≠ source)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source)
    (fiber : PeriodicHypercubicEvenSpatialSliceLink H)
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
        f g =
      realIntegralCovariance
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta
            (Function.update (Function.update B source k) target g2))
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
            H N hN beta hbeta B target source fiber k g2 f)
          g +
        realIntegralCovariance
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta
            (Function.update (Function.update B source k) target g2))
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
            H N hN beta hbeta B target source fiber k g2 f)
          g := by
  let mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta
      (Function.update (Function.update B source k) target g2)
  have hPf :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_memLp_two
      H N hN beta hbeta B hne hNoShare fiber k g2 f hf
  have hSub :
      realIntegralCovariance mu
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
            H N hN beta hbeta B target source fiber k g2 f)
          g =
        realIntegralCovariance mu f g -
          realIntegralCovariance mu
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
              H N hN beta hbeta B target source fiber k g2 f)
            g := by
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation] using
      realIntegralCovariance_sub_left_of_memLp_two
        mu
        f
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
          H N hN beta hbeta B target source fiber k g2 f)
        g hf hPf hg
  change
    realIntegralCovariance mu f g =
      realIntegralCovariance mu
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
            H N hN beta hbeta B target source fiber k g2 f)
          g +
        realIntegralCovariance mu
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
            H N hN beta hbeta B target source fiber k g2 f)
          g
  linarith

/-- Exact right-slot covariance decomposition g = P g + Q g for the actual
remote kernel-section one-link projection and fluctuation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_add_fluctuation_realIntegralCovariance_right_of_memLp_two
    (H N : Nat)
    (hN : 0 < N)
    (beta : Real)
    (hbeta : 0 <= beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hne : target ≠ source)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source)
    (fiber : PeriodicHypercubicEvenSpatialSliceLink H)
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
        f g =
      realIntegralCovariance
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta
            (Function.update (Function.update B source k) target g2))
          f
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
            H N hN beta hbeta B target source fiber k g2 g) +
        realIntegralCovariance
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta
            (Function.update (Function.update B source k) target g2))
          f
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
            H N hN beta hbeta B target source fiber k g2 g) := by
  let mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta
      (Function.update (Function.update B source k) target g2)
  have hPg :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_memLp_two
      H N hN beta hbeta B hne hNoShare fiber k g2 g hg
  have hSub :
      realIntegralCovariance mu f
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
            H N hN beta hbeta B target source fiber k g2 g) =
        realIntegralCovariance mu f g -
          realIntegralCovariance mu f
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
              H N hN beta hbeta B target source fiber k g2 g) := by
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation] using
      realIntegralCovariance_sub_right_of_memLp_two
        mu
        g
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
          H N hN beta hbeta B target source fiber k g2 g)
        f hg hPg hf
  change
    realIntegralCovariance mu f g =
      realIntegralCovariance mu f
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
            H N hN beta hbeta B target source fiber k g2 g) +
        realIntegralCovariance mu f
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
            H N hN beta hbeta B target source fiber k g2 g)
  linarith

end

end MathlibAnalytic
end MGAP4D
