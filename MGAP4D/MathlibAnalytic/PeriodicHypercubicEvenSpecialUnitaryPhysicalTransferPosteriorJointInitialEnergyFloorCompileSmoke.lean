import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointRightAnchoredMajorant

/-! Regression contracts for prefix floors and the constructed centered alternative. -/
namespace MGAP4D.MathlibAnalytic

open MeasureTheory GroundStatePosteriorJoint
open scoped BigOperators

noncomputable section

attribute [local instance]
  groundStateJointOneLinkBoundedCoreSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkBoundedCoreSpecialUnitaryCompactSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkBoundedCoreSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitaryBorelSpace
  groundStateJointOneLinkBoundedCoreSpatialLinkFintype

#check GroundStatePosteriorJoint.posteriorVariationSchedule_ge_of_not_mem
#check GroundStatePosteriorJoint.initialVariation_le_sixColorVariationProfile
#check GroundStatePosteriorJoint.initialOscillationEnergy_le_prefixEnergy
#check GroundStatePosteriorJoint.uniformPrefixEnergy_ge_card_mul_norm_sq
#check GroundStatePosteriorJoint.norm_sq_le_uniformBCFApproximationMajorant
#check GroundStatePosteriorJoint.norm_sq_isLeast_uniformBCFApproximationMajorants
#check GroundStatePosteriorJoint.sixColorProfileEnergy_le_rightAnchoredMajorant
#check GroundStatePosteriorJoint.sixColorProfileEnergy_sub_rightAnchor

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "JL2" => PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta
local notation "RData" => PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteExpectationResponseMatrixData H N hN beta hbeta
local notation "Rep" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF H N hN beta hbeta
local notation "Profile" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy H N hN beta hbeta
local notation "Osc" => periodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageOscillationEnergy H
local notation "Delta" => posteriorSixColorVariationProfile H N hN beta hbeta
local notation "A" => bcfApproximationMajorant H N hN beta hbeta

example (c : Link → Link → ℝ) (v : Link → ℝ) (e : Link) :
    posteriorVariationSchedule H c [] v e = v e := rfl

example (c : Link → Link → ℝ) (v : Link → ℝ) (e : Link) :
    posteriorVariationSchedule H c [e] v e = 0 := by
  simpa using posteriorVariationSchedule_append_target H c [] e v

example (c : Link → Link → ℝ) (pre : List Link) :
    posteriorVariationSchedule H c pre (fun _ => 0) = (fun _ => 0) :=
  posteriorVariationSchedule_zero H c pre

example (R : RData) (v : Link → ℝ) (hv : ∀ e, 0 ≤ v e) (e : Link) :
    v e ≤ Delta R v e := initialVariation_le_sixColorVariationProfile H N hN beta hbeta R v hv e

example (R : RData) (v : Link → ℝ) (hv : ∀ e, 0 ≤ v e) (s : Finset Link) :
    (1 / 6 : ℝ) * (∑ e ∈ s, v e ^ 2) ≤ Osc (Delta R v) :=
  initialSupportEnergy_le_prefixEnergy H N hN beta hbeta R v hv s

example (R : RData) (O : BoundedContinuousFunction Joint ℝ) (f : JL2) :
    ‖f‖ ^ 2 ≤ A R O (fun _ => 2 * ‖O‖) f :=
  norm_sq_le_uniformBCFApproximationMajorant H N hN beta hbeta R O f

example (R : RData) (f : JL2) : A R 0 (fun _ => 0) f = ‖f‖ ^ 2 :=
  uniformBCFApproximationMajorant_zero H N hN beta hbeta R f

example (R : RData) (O : BoundedContinuousFunction Joint ℝ) (f : JL2) :
    Profile f ≤ A R O (rightAnchoredInitialVariation H N O) f :=
  sixColorProfileEnergy_le_rightAnchoredMajorant H N hN beta hbeta R O f

example (R : RData) (O : BoundedContinuousFunction Joint ℝ) :
    Continuous (A R O (rightAnchoredInitialVariation H N O)) :=
  bcfApproximationMajorant_continuous H N hN beta hbeta R O _

example (a : ℝ) (e : Link) :
    rightAnchoredInitialVariation H N (BoundedContinuousFunction.const Joint a) e = 0 := by
  have hAnchor : posteriorRightAnchorBCF H N (BoundedContinuousFunction.const Joint a) =
      BoundedContinuousFunction.const Joint a := by ext z; rfl
  simp [rightAnchoredInitialVariation, hAnchor]

example (R : RData) (a : ℝ) : Profile (Rep (BoundedContinuousFunction.const Joint a)) = 0 := by
  have hAnchor : posteriorRightAnchorBCF H N (BoundedContinuousFunction.const Joint a) =
      BoundedContinuousFunction.const Joint a := by ext z; rfl
  simpa only [hAnchor] using sixColorProfileEnergy_rightAnchor_eq_zero H N hN beta hbeta R
    (BoundedContinuousFunction.const Joint a)

example (R : RData) (O : BoundedContinuousFunction Joint ℝ) (f : JL2) :
    Profile (f - Rep (posteriorRightAnchorBCF H N O)) = Profile f :=
  sixColorProfileEnergy_sub_rightAnchor H N hN beta hbeta R O f

#print axioms GroundStatePosteriorJoint.posteriorVariationSchedule_ge_of_not_mem
#print axioms GroundStatePosteriorJoint.posteriorVariationSchedule_zero
#print axioms GroundStatePosteriorJoint.initialVariation_le_sixColorVariationProfile
#print axioms GroundStatePosteriorJoint.initialSupportEnergy_le_prefixEnergy
#print axioms GroundStatePosteriorJoint.uniformPrefixEnergy_ge_card_mul_norm_sq
#print axioms GroundStatePosteriorJoint.posteriorSpatialLink_card_ge_two
#print axioms GroundStatePosteriorJoint.jointBCFRepresentative_norm_le_sup
#print axioms GroundStatePosteriorJoint.norm_sq_isLeast_uniformBCFApproximationMajorants
#print axioms GroundStatePosteriorJoint.posteriorRightAnchorBCF_idempotent
#print axioms GroundStatePosteriorJoint.rightAnchoredInitialVariation_bound
#print axioms GroundStatePosteriorJoint.sixColorProfileEnergy_le_rightAnchoredMajorant
#print axioms GroundStatePosteriorJoint.rightAnchoredMajorant_at_anchor
#print axioms GroundStatePosteriorJoint.sixColorResidualOperator_rightAnchor_eq_zero
#print axioms GroundStatePosteriorJoint.sixColorProfileEnergy_sub_rightAnchor

end
end MGAP4D.MathlibAnalytic
