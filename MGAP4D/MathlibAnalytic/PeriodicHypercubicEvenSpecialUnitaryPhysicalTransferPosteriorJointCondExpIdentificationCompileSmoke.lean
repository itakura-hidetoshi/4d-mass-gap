import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointCondExpIdentification

/-! Independent bounded-core contract for the literal posterior integral. -/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory

attribute [local instance]
  groundStateJointOneLinkBoundedCoreSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkBoundedCoreSpecialUnitaryCompactSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkBoundedCoreSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitaryBorelSpace
  groundStateJointOneLinkBoundedCoreSpatialLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkUnique

example (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (fun z => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
      H N hN beta hbeta target
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
        H N hN beta hbeta F hF bound hbound) z) =ᵐ[
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure H N hN beta hbeta]
      fun z => ∫ g, F (z.1, Function.update z.2 target g)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
          H N hN beta hbeta z.1 z.2 target := by
  exact GroundStatePosteriorJoint.condExpL2_coeFn_eq_posteriorMean
    H N hN beta hbeta target F hF bound hbound

#check GroundStatePosteriorJoint.canonicalKernel_map_joint_ae_eq_posterior
#check GroundStatePosteriorJoint.canonicalMean_joint_ae_eq_posteriorMean
#check GroundStatePosteriorJoint.condExpL2_coeFn_eq_posteriorMean
#check GroundStatePosteriorJoint.posteriorMean_memLp_two
#check GroundStatePosteriorJoint.posteriorMeanL2_eq_condExpL2
#check GroundStatePosteriorJoint.condExpL2_coeFn_eq_posteriorBCF

#print axioms GroundStatePosteriorJoint.canonicalKernel_map_joint_ae_eq_posterior
#print axioms GroundStatePosteriorJoint.canonicalMean_joint_ae_eq_posteriorMean
#print axioms GroundStatePosteriorJoint.condExpL2_coeFn_eq_posteriorMean
#print axioms GroundStatePosteriorJoint.posteriorMean_memLp_two
#print axioms GroundStatePosteriorJoint.posteriorMeanL2_eq_condExpL2
#print axioms GroundStatePosteriorJoint.condExpL2_coeFn_eq_posteriorBCF

end MGAP4D.MathlibAnalytic
