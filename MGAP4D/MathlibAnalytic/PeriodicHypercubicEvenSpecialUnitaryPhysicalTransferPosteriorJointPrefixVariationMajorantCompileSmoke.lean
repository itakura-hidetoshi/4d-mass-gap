import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointPrefixVariationMajorant

/-! Regression contracts for constructed, rather than assumed, prefix residual bounds. -/

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
local notation "Raw" => posteriorSchedule H N hN beta hbeta
local notation "Energy" => posteriorStageResidualEnergy H N hN beta hbeta

example (c : Link → Link → ℝ) (v : Link → ℝ) :
    posteriorVariationSchedule H c [] v = v := rfl

-- The last target is erased exactly, including repeated updates.
example (c : Link → Link → ℝ) (pre : List Link) (target : Link) (v : Link → ℝ) :
    posteriorVariationSchedule H c (pre ++ [target]) v target = 0 :=
  posteriorVariationSchedule_append_target H c pre target v

-- Regularity belongs to the literal intermediate function at every fixed left boundary.
example (pre : List Link) (F : BoundedContinuousFunction Joint ℝ) (B : Cfg) :
    Continuous (fun A => Raw pre F (B, A)) :=
  posteriorSchedule_left_continuous H N hN beta hbeta pre F B

-- No final residual bound is an input. General H and positive N are retained.
example (s : ℝ) (hs : 1 ≤ s)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff s)
    (pre : List Link) (target : Link) (F : BoundedContinuousFunction Joint ℝ) :
    Energy pre target F ≤
      canonicalPosteriorPrefixVariation H N hN beta hbeta s hs hcut pre
        (fun _ => 2 * ‖F‖) target ^ 2 :=
  posteriorStageResidualEnergy_le_canonicalUniformPrefixVariation_sq
    H N hN beta hbeta s hs hcut pre target F

-- The actual original joint projection residual receives the constructed bound.
example (s : ℝ) (hs : 1 ≤ s)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff s)
    (pre : List Link) (target : Link) (F : BoundedContinuousFunction Joint ℝ) :
    ‖posteriorScheduleL2 H N hN beta hbeta pre F F.continuous.stronglyMeasurable
        ‖F‖ F.norm_coe_le_norm -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
        H N hN beta hbeta target
        (posteriorScheduleL2 H N hN beta hbeta pre F F.continuous.stronglyMeasurable
          ‖F‖ F.norm_coe_le_norm)‖ ^ 2 ≤
      canonicalPosteriorPrefixVariation H N hN beta hbeta s hs hcut pre
        (fun _ => 2 * ‖F‖) target ^ 2 := by
  rw [← posteriorStageResidualEnergy_eq_projectionResidualNormSq
    H N hN beta hbeta pre target F F.continuous.stronglyMeasurable ‖F‖ F.norm_coe_le_norm]
  exact posteriorStageResidualEnergy_le_canonicalUniformPrefixVariation_sq
    H N hN beta hbeta s hs hcut pre target F

#check GroundStatePosteriorJoint.posteriorSliceSchedule_variation_abs_le
#check GroundStatePosteriorJoint.posteriorSliceSchedule_eq_posteriorSchedule
#check GroundStatePosteriorJoint.posteriorSchedule_variation_abs_le
#check GroundStatePosteriorJoint.posteriorStageResidual_abs_le_variationSchedule
#check GroundStatePosteriorJoint.posteriorStageResidualEnergy_le_variationSchedule_sq
#check GroundStatePosteriorJoint.posteriorStageResidual_abs_le_canonicalPrefixVariation
#check GroundStatePosteriorJoint.posteriorStageResidualEnergy_le_canonicalPrefixVariation_sq

#print axioms GroundStatePosteriorJoint.posteriorVariationSchedule_nonneg
#print axioms GroundStatePosteriorJoint.posteriorVariationSchedule_append_target
#print axioms GroundStatePosteriorJoint.posteriorSliceSchedule_variation_abs_le
#print axioms GroundStatePosteriorJoint.posteriorSliceSchedule_eq_posteriorSchedule
#print axioms GroundStatePosteriorJoint.posteriorSchedule_left_continuous
#print axioms GroundStatePosteriorJoint.posteriorSchedule_variation_abs_le
#print axioms GroundStatePosteriorJoint.posteriorStageResidual_abs_le_variationSchedule
#print axioms GroundStatePosteriorJoint.posteriorStageResidualEnergy_le_variationSchedule_sq
#print axioms GroundStatePosteriorJoint.posteriorStageResidual_abs_le_canonicalPrefixVariation
#print axioms GroundStatePosteriorJoint.posteriorStageResidualEnergy_le_canonicalPrefixVariation_sq
#print axioms GroundStatePosteriorJoint.jointBCF_variation_le_two_norm
#print axioms GroundStatePosteriorJoint.posteriorStageResidualEnergy_le_canonicalUniformPrefixVariation_sq

end

end MGAP4D.MathlibAnalytic
