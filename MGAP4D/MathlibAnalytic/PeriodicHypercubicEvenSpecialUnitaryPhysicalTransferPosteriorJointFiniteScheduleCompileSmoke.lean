import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointFiniteSchedule

/-! Regression contracts for chronological literal posterior finite schedules. -/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory

noncomputable section

attribute [local instance]
  groundStateJointOneLinkBoundedCoreSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkBoundedCoreSpecialUnitaryCompactSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkBoundedCoreSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitaryBorelSpace
  groundStateJointOneLinkBoundedCoreSpatialLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkUnique

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "μJ" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure H N hN beta hbeta
local notation "PJoint" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2 H N hN beta hbeta
local notation "νPost" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure H N hN beta hbeta

-- The public endpoint uses the original joint Hilbert carrier and projection sweep.
example (order : List Link) (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    GroundStatePosteriorJoint.posteriorScheduleL2 H N hN beta hbeta order F hF bound hbound =
      realHilbertProjectionSweep PJoint order
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
          H N hN beta hbeta F hF bound hbound) := by
  exact GroundStatePosteriorJoint.posteriorScheduleL2_eq_projectionSchedule
    H N hN beta hbeta order F hF bound hbound

-- The first listed projection acts first; the inner fiber sees the updated environment.
-- The two links are arbitrary and may coincide.
example (first second : Link) (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (fun z => PJoint second (PJoint first
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
        H N hN beta hbeta F hF bound hbound)) z) =ᵐ[μJ]
    (fun z => ∫ g2,
      (∫ g1, F (z.1, Function.update (Function.update z.2 second g2) first g1)
        ∂νPost z.1 (Function.update z.2 second g2) first)
      ∂νPost z.1 z.2 second) := by
  exact GroundStatePosteriorJoint.projectionSchedule_coeFn_eq_posteriorSchedule
    H N hN beta hbeta [first, second] F hF bound hbound

example (F : Joint → ℝ) :
    GroundStatePosteriorJoint.posteriorSchedule H N hN beta hbeta [] F = F := by
  rfl

-- Null-set changes remain invisible even after a repeated-target schedule.
example (first second : Link) (F G : Joint → ℝ) (hFG : F =ᵐ[μJ] G) :
    GroundStatePosteriorJoint.posteriorSchedule H N hN beta hbeta [first, second, first] F =ᵐ[μJ]
      GroundStatePosteriorJoint.posteriorSchedule H N hN beta hbeta [first, second, first] G := by
  exact GroundStatePosteriorJoint.posteriorSchedule_congr_ae
    H N hN beta hbeta [first, second, first] hFG

#check GroundStatePosteriorJoint.canonicalMean_congr_ae
#check GroundStatePosteriorJoint.posteriorMean_congr_ae
#check GroundStatePosteriorJoint.posteriorSchedule_congr_ae
#check GroundStatePosteriorJoint.posteriorSchedule_ae_eq_canonicalSchedule
#check GroundStatePosteriorJoint.canonicalScheduleL2_eq_projectionSchedule
#check GroundStatePosteriorJoint.projectionSchedule_coeFn_eq_posteriorSchedule
#check GroundStatePosteriorJoint.posteriorSchedule_memLp_two
#check GroundStatePosteriorJoint.posteriorScheduleL2_eq_projectionSchedule

#print axioms GroundStatePosteriorJoint.canonicalMean_congr_ae
#print axioms GroundStatePosteriorJoint.posteriorMean_congr_ae
#print axioms GroundStatePosteriorJoint.posteriorSchedule_congr_ae
#print axioms GroundStatePosteriorJoint.posteriorSchedule_ae_eq_canonicalSchedule
#print axioms GroundStatePosteriorJoint.canonicalScheduleL2_eq_projectionSchedule
#print axioms GroundStatePosteriorJoint.projectionSchedule_coeFn_eq_posteriorSchedule
#print axioms GroundStatePosteriorJoint.posteriorSchedule_memLp_two
#print axioms GroundStatePosteriorJoint.posteriorScheduleL2_eq_projectionSchedule

end

end MGAP4D.MathlibAnalytic
