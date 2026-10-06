import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointStageResidualEnergy

/-! Regression contracts for exact literal posterior stage energy. -/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory GroundStatePosteriorJoint

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
local notation "Raw" => posteriorSchedule H N hN beta hbeta
local notation "StageL2" => posteriorScheduleL2 H N hN beta hbeta
local notation "Energy" => posteriorStageResidualEnergy H N hN beta hbeta

-- The literal integral, not merely an opaque energy wrapper, is tested against
-- the original ordered joint projection sweep. The prefix may repeat target.
example (pre : List Link) (target : Link)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (∫ z, (Raw pre F z -
      ∫ g, Raw pre F (z.1, Function.update z.2 target g)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
          H N hN beta hbeta z.1 z.2 target) ^ 2 ∂μJ) =
    ‖realHilbertProjectionSweep PJoint pre
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
          H N hN beta hbeta F hF bound hbound) -
      PJoint target (realHilbertProjectionSweep PJoint pre
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
          H N hN beta hbeta F hF bound hbound))‖ ^ 2 := by
  simpa only [posteriorStageResidualEnergy, posteriorStageResidual,
    posteriorSchedule_append_singleton, posteriorMean, posteriorScheduleL2_eq_projectionSchedule] using
    posteriorStageResidualEnergy_eq_projectionResidualNormSq
      H N hN beta hbeta pre target F hF bound hbound

-- Two chronological stage energies telescope even when the links coincide.
-- This is norm loss, not the squared norm of the total vector defect.
example (first second : Link) (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    Energy [] first F + Energy [first] second F =
      ‖StageL2 [] F hF bound hbound‖ ^ 2 -
        ‖StageL2 [first, second] F hF bound hbound‖ ^ 2 := by
  rw [posteriorStageResidualEnergy_eq_norm_loss H N hN beta hbeta [] first F hF bound hbound,
    posteriorStageResidualEnergy_eq_norm_loss H N hN beta hbeta [first] second F hF bound hbound]
  simp only [List.nil_append, List.cons_append]
  ring

example (pre : List Link) (target : Link)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound)
    (b : Joint → ℝ) (hb : MemLp b 2 μJ)
    (hdom : ∀ᵐ z ∂μJ,
      ‖posteriorStageResidual H N hN beta hbeta pre target F z‖ ≤ ‖b z‖) :
    Energy pre target F ≤ ∫ z, b z ^ 2 ∂μJ := by
  exact posteriorStageResidualEnergy_le_of_ae_majorant
    H N hN beta hbeta pre target F hF bound hbound b hb hdom

example (pre : List Link) (target : Link)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound)
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (hdom : ∀ᵐ z ∂μJ,
      ‖posteriorStageResidual H N hN beta hbeta pre target F z‖ ≤ delta) :
    Energy pre target F ≤ delta ^ 2 := by
  exact posteriorStageResidualEnergy_le_of_ae_bound
    H N hN beta hbeta pre target F hF bound hbound delta hdelta hdom

#check GroundStatePosteriorJoint.posteriorSchedule_append_singleton
#check GroundStatePosteriorJoint.projectionStageResidual_coeFn_eq_posteriorStageResidual
#check GroundStatePosteriorJoint.posteriorStageResidual_memLp_two
#check GroundStatePosteriorJoint.posteriorStageResidualEnergy_eq_projectionResidualNormSq
#check GroundStatePosteriorJoint.posteriorStageResidualEnergy_eq_norm_loss
#check GroundStatePosteriorJoint.posteriorStageResidualEnergy_le_of_ae_majorant
#check GroundStatePosteriorJoint.posteriorStageResidualEnergy_le_of_ae_bound

#print axioms GroundStatePosteriorJoint.posteriorSchedule_append_singleton
#print axioms GroundStatePosteriorJoint.posteriorScheduleL2_append_singleton
#print axioms GroundStatePosteriorJoint.projectionStageResidual_coeFn_eq_posteriorStageResidual
#print axioms GroundStatePosteriorJoint.posteriorStageResidual_memLp_two
#print axioms GroundStatePosteriorJoint.posteriorStageResidual_sq_integrable
#print axioms GroundStatePosteriorJoint.posteriorStageResidualEnergy_eq_projectionResidualNormSq
#print axioms GroundStatePosteriorJoint.posteriorStageResidualEnergy_eq_norm_loss
#print axioms GroundStatePosteriorJoint.posteriorStageResidualEnergy_nonneg
#print axioms GroundStatePosteriorJoint.posteriorStageResidualEnergy_le_of_ae_majorant
#print axioms GroundStatePosteriorJoint.posteriorStageResidualEnergy_le_of_ae_bound

end

end MGAP4D.MathlibAnalytic
