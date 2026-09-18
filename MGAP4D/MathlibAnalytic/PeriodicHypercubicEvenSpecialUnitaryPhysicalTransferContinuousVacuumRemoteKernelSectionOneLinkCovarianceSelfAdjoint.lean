import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumRemoteKernelSectionOneLinkProjection
import MGAP4D.MathlibAnalytic.RealConditionalExpectationCovarianceSelfAdjoint
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory

noncomputable section

local instance remoteKernelSectionOneLinkCovarianceSelfAdjointSpecialUnitaryMeasurableSpace
    (N : Nat) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) Complex) :=
  specialUnitaryGroupMeasurableSpace N

local instance remoteKernelSectionOneLinkCovarianceSelfAdjointSpatialLinkFintype
    (H : Nat) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance remoteKernelSectionOneLinkCovarianceSelfAdjointKernelSectionProbabilityMeasure
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

/-- The actual remote kernel-section one-link heat-bath projection is
self-adjoint for ordinary real covariance on square-integrable observables.

The proof uses the exact almost-everywhere identification of the pointwise
heat-bath projection with conditional expectation and the generic
measure-theoretic self-adjointness theorem.  No Gibbs-law identification is
used. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_realIntegralCovariance_symm_of_memLp_two
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
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
          H N hN beta hbeta B target source fiber k g2 f)
        g =
      realIntegralCovariance
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta
          (Function.update (Function.update B source k) target g2))
        f
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
          H N hN beta hbeta B target source fiber k g2 g) := by
  let mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta
      (Function.update (Function.update B source k) target g2)
  have hfInt : Integrable f mu :=
    memLp_one_iff_integrable.1 (hf.mono_exponent one_le_two)
  have hgInt : Integrable g mu :=
    memLp_one_iff_integrable.1 (hg.mono_exponent one_le_two)
  have hProjectionF :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_ae_eq_condExp
      H N hN beta hbeta B hne hNoShare fiber k g2 f hfInt
  have hProjectionG :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_ae_eq_condExp
      H N hN beta hbeta B hne hNoShare fiber k g2 g hgInt
  change
    realIntegralCovariance mu
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
          H N hN beta hbeta B target source fiber k g2 f) g =
      realIntegralCovariance mu f
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
          H N hN beta hbeta B target source fiber k g2 g)
  calc
    realIntegralCovariance mu
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
          H N hN beta hbeta B target source fiber k g2 f) g =
      realIntegralCovariance mu (MeasureTheory.condExp
        (periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace H N fiber)
        mu f) g := by
        exact realIntegralCovariance_congr_left_ae mu hProjectionF
    _ = realIntegralCovariance mu f (MeasureTheory.condExp
        (periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace H N fiber)
        mu g) := by
      exact
        realIntegralCovariance_condExp_symm_of_memLp_two
          mu
          (periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace H N fiber)
          (periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace_le H N fiber)
          f g hf hg
    _ = realIntegralCovariance mu f
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
          H N hN beta hbeta B target source fiber k g2 g) := by
      exact (realIntegralCovariance_congr_right_ae mu hProjectionG).symm

end

end MathlibAnalytic
end MGAP4D
