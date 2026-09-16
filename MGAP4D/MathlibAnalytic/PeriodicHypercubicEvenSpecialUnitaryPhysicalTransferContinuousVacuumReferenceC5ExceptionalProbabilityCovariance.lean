import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceC5ExceptionalSupport
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumRemoteNoShareProbabilityCovarianceLocalization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance physicalContinuousVacuumC5ExceptionalProbabilityCovarianceSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- Outside the volume-independent C5 exceptional set, the remaining remote
four-point defect is an ordinary covariance of two one-link observables under
the normalized fixed-right ground-state kernel-section probability law.

Together with the exceptional-set cardinality bound `≤ 20`, this gives the
precise decomposition needed for a volume-uniform residual estimate: the bare
Wilson contribution is confined to a uniformly finite set, while every remote
term is a probability covariance.  No covariance-decay estimate is asserted
here. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_remote_crossRatio_defect_eq_sourceSpatialRatio_mul_mass_sq_mul_probabilityCovariance_of_not_mem_C5Exceptional
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (fiber distinguishedTarget backgroundFiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (hRemote : backgroundFiber ∉
      periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers
        H fiber distinguishedTarget)
    (h k g₁ g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta
          (Function.update (Function.update B fiber h) backgroundFiber g₁)) *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta
          (Function.update (Function.update B fiber k) backgroundFiber g₂)) -
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta
          (Function.update (Function.update B fiber k) backgroundFiber g₁)) *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta
          (Function.update (Function.update B fiber h) backgroundFiber g₂)) =
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
          H N beta B fiber h /
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
          H N beta B fiber k) *
      ((‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN beta hbeta‖ *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta
            (Function.update (Function.update B fiber k) backgroundFiber g₂)) ^ 2 *
        realIntegralCovariance
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionProbabilityMeasure
            H N hN beta hbeta
            (Function.update (Function.update B fiber k) backgroundFiber g₂))
          (fun A =>
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                H N beta A B backgroundFiber g₁ /
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                H N beta A B backgroundFiber g₂)
          (fun A =>
            specialUnitaryWilsonRelativeKernel N beta (A fiber) h /
              specialUnitaryWilsonRelativeKernel N beta (A fiber) k)) := by
  rcases
    periodicHypercubicEvenSpatialSlice_not_mem_C5ExceptionalBackgroundFibers
      H fiber distinguishedTarget backgroundFiber hRemote with
    ⟨hFiberBackground, _hBackgroundTarget, hNoShare⟩
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_remote_noShare_crossRatio_defect_eq_sourceSpatialRatio_mul_mass_sq_mul_probabilityCovariance
      H N hN beta hbeta B (target := backgroundFiber) (source := fiber)
      (Ne.symm hFiberBackground) hNoShare h k g₁ g₂

end

end MathlibAnalytic
end MGAP4D
