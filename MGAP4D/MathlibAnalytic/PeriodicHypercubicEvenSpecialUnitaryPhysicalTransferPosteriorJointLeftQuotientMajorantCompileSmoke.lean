import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPosteriorLeftQuotientMajorant

/-! Regression contracts for intrinsic centering on the unchanged joint carrier. -/
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

#check GroundStatePosteriorJoint.sixColorResidualOperator_coarse_eq_zero
#check GroundStatePosteriorJoint.sixColorProfileEnergy_sub_coarse
#check GroundStatePosteriorJoint.leftCenteredError_isLeast
#check GroundStatePosteriorJoint.sixColorProfileEnergy_le_leftQuotientMajorant
#check GroundStatePosteriorJoint.leftQuotientMajorant_le_bcfApproximationMajorant
#check GroundStatePosteriorJoint.leftCenteredError_pythagoras
#check GroundStatePosteriorJoint.leftQuotientMajorant_isLeast
#check GroundStatePosteriorJoint.sixColorProfileEnergy_le_leftCenteredNormSq
#check GroundStatePosteriorJoint.fineFrozenProfileEnergy_le_leftCenteredNormSq
#check GroundStatePosteriorJoint.fineFrozenProfileEnergy_le_leftQuotientMajorant
#check GroundStatePosteriorJoint.fineFrozenProfileEnergy_le_of_leftQuotientApproximation
#check GroundStatePosteriorJoint.fineFrozenProfileEnergy_le_canonicalLeftQuotientMajorant

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "JL2" => PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta
local notation "VL2" => PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateVacuumL2 H N hN beta hbeta
local notation "JLeft" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftBoundaryL2Isometry H N hN beta hbeta
local notation "ALeft" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftBoundaryAdjoint H N hN beta hbeta
local notation "QLeft" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCoarseCondExp H N hN beta hbeta
local notation "PJoint" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2 H N hN beta hbeta
local notation "Center" => posteriorLeftCenteredOperator H N hN beta hbeta
local notation "T" => sixColorResidualOperator H N hN beta hbeta
local notation "Profile" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy H N hN beta hbeta
local notation "BCFRep" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF H N hN beta hbeta
local notation "ResponseData" => PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteExpectationResponseMatrixData H N hN beta hbeta
local notation "Majorant" => leftQuotientMajorant H N hN beta hbeta
local notation "OscEnergy" => periodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageOscillationEnergy H

example (e : Link) (u : VL2) : PJoint e (JLeft u) = JLeft u :=
  posteriorOneLink_leftBoundary_fixed H N hN beta hbeta e u

example (e : Link) (u : VL2) : realHilbertProjectionSweep PJoint [e, e] (JLeft u) = JLeft u :=
  posteriorProjectionSchedule_leftBoundary_fixed H N hN beta hbeta [e, e] u

example (f : JL2) : T (QLeft f) = 0 :=
  sixColorResidualOperator_coarse_eq_zero H N hN beta hbeta f

example (f : JL2) : ‖Center f‖ ≤ ‖f‖ :=
  posteriorLeftCenteredOperator_norm_le H N hN beta hbeta f

example (f : JL2) : Center (Center f) = Center f :=
  posteriorLeftCenteredOperator_idempotent H N hN beta hbeta f

example (u : VL2) : Center (JLeft u) = 0 :=
  posteriorLeftCenteredOperator_leftBoundary H N hN beta hbeta u

example (f g : JL2) : Profile (f - QLeft g) = Profile f :=
  sixColorProfileEnergy_sub_coarse H N hN beta hbeta f g

example (f g : JL2) (u : VL2) : ‖f - g - JLeft u‖ ^ 2 =
    ‖Center (f - g)‖ ^ 2 + ‖QLeft (f - g) - JLeft u‖ ^ 2 :=
  leftCenteredError_pythagoras H N hN beta hbeta f g u

example (f g : JL2) (u : VL2) : ‖Center (f - g)‖ ≤ ‖f - g - JLeft u‖ :=
  (leftCenteredError_isLeast H N hN beta hbeta f g).2 ⟨u, rfl⟩

example (f g : JL2) : ‖Center (f - g)‖ ^ 2 = ‖f - g‖ ^ 2 - ‖ALeft (f - g)‖ ^ 2 :=
  leftCenteredError_norm_sq H N hN beta hbeta f g

example (R : ResponseData) (O : BoundedContinuousFunction Joint ℝ) (v : Link → ℝ) (f : JL2) :
    Majorant R O v f ≤ bcfApproximationMajorant H N hN beta hbeta R O v f :=
  leftQuotientMajorant_le_bcfApproximationMajorant H N hN beta hbeta R O v f

example (R : ResponseData) (O : BoundedContinuousFunction Joint ℝ) (v : Link → ℝ) :
    Continuous (Majorant R O v) := leftQuotientMajorant_continuous H N hN beta hbeta R O v

example (R : ResponseData) (u : VL2) : Majorant R 0 (fun _ => 0) (JLeft u) = 0 := by
  rw [leftQuotientMajorant_zero, posteriorLeftCenteredOperator_leftBoundary, norm_zero, zero_pow (by decide)]

example (R : ResponseData) (O : BoundedContinuousFunction Joint ℝ) (v : Link → ℝ)
    (f : JL2) (u : VL2) : Majorant R O v (f + JLeft u) = Majorant R O v f :=
  leftQuotientMajorant_add_leftBoundary H N hN beta hbeta R O v f u

example (f : JL2) : ‖Center (f - f)‖ = 0 := by simp only [sub_self, map_zero, norm_zero]

example (R : ResponseData) (O : BoundedContinuousFunction Joint ℝ)
    (v : Link → ℝ) (hv : ∀ e, 0 ≤ v e)
    (hV : ∀ (B : Cfg) (e : Link) (A C : Cfg),
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorAgreeOff A C e →
        |O (B, A) - O (B, C)| ≤ v e)
    (f : JL2) (epsilon amplitude : ℝ) (ha : 0 ≤ amplitude)
    (he : ‖Center (f - BCFRep O)‖ ≤ epsilon)
    (hvE : OscEnergy (posteriorSixColorVariationProfile H N hN beta hbeta R v) ≤ amplitude ^ 2) :
    Profile f ≤ (epsilon + amplitude) ^ 2 :=
  sixColorProfileEnergy_le_of_leftQuotientApproximation H N hN beta hbeta R O v hv hV f epsilon amplitude ha he hvE

#print axioms GroundStatePosteriorJoint.posteriorOneLink_leftBoundary_fixed
#print axioms GroundStatePosteriorJoint.posteriorProjectionSchedule_leftBoundary_fixed
#print axioms GroundStatePosteriorJoint.sixColorResidualOperator_leftBoundary_eq_zero
#print axioms GroundStatePosteriorJoint.sixColorResidualOperator_coarse_eq_zero
#print axioms GroundStatePosteriorJoint.sixColorProfileEnergy_sub_coarse
#print axioms GroundStatePosteriorJoint.posteriorLeftCenteredOperator_norm_le
#print axioms GroundStatePosteriorJoint.leftCenteredError_pythagoras
#print axioms GroundStatePosteriorJoint.leftCenteredError_isLeast
#print axioms GroundStatePosteriorJoint.leftCenteredError_norm_sq
#print axioms GroundStatePosteriorJoint.leftQuotientMajorant_continuous
#print axioms GroundStatePosteriorJoint.leftQuotientMajorant_le_bcfApproximationMajorant
#print axioms GroundStatePosteriorJoint.leftQuotientMajorant_isLeast
#print axioms GroundStatePosteriorJoint.sixColorProfileEnergy_le_leftQuotientMajorant
#print axioms GroundStatePosteriorJoint.sixColorProfileEnergy_le_leftQuotientRightAnchoredMajorant
#print axioms GroundStatePosteriorJoint.fineFrozenProfileEnergy_le_leftCenteredNormSq
#print axioms GroundStatePosteriorJoint.fineFrozenProfileEnergy_le_leftQuotientMajorant
#print axioms GroundStatePosteriorJoint.fineFrozenProfileEnergy_le_of_leftQuotientApproximation
#print axioms GroundStatePosteriorJoint.fineFrozenProfileEnergy_le_canonicalLeftQuotientMajorant

end

end MGAP4D.MathlibAnalytic
