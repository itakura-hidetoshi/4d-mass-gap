import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPosteriorBCFApproximationMajorant

/-! Compile contracts for the sharp P3 quantitative L2 approximation bridge. -/

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

#check GroundStatePosteriorJoint.sixColorResidualOperator_norm_sq
#check GroundStatePosteriorJoint.sixColorProfileAmplitude_lipschitz
#check GroundStatePosteriorJoint.sixColorProfileEnergy_le_bcfApproximationMajorant
#check GroundStatePosteriorJoint.bcfApproximationMajorant_continuous
#check GroundStatePosteriorJoint.sixColorProfileEnergy_le_of_bcfApproximation
#check GroundStatePosteriorJoint.fineFrozenProfileEnergy_le_bcfApproximationMajorant
#check GroundStatePosteriorJoint.fineFrozenProfileEnergy_le_of_bcfApproximation
#check GroundStatePosteriorJoint.fineFrozenProfileEnergy_le_canonicalBCFApproximationMajorant

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "JL2" => PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta
local notation "Profile" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy H N hN beta hbeta
local notation "BCFRep" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF H N hN beta hbeta
local notation "ResponseData" => PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteExpectationResponseMatrixData H N hN beta hbeta
local notation "T" => sixColorResidualOperator H N hN beta hbeta
local notation "Amp" => sixColorProfileAmplitude H N hN beta hbeta
local notation "OscEnergy" => periodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageOscillationEnergy H

example (f : JL2) : ‖T f‖ ^ 2 = Profile f :=
  sixColorResidualOperator_norm_sq H N hN beta hbeta f

example (f g : JL2) : T (f + g) = T f + T g := map_add T f g

example (f g : JL2) : T (f - g) = T f - T g := map_sub T f g

example : Profile (0 : JL2) = 0 := by
  rw [← sixColorResidualOperator_norm_sq]
  simp

example (f : JL2) : Amp f ^ 2 = Profile f :=
  Real.sq_sqrt (sixColorProfileEnergy_nonneg H N hN beta hbeta f)

example (f g : JL2) : dist (Amp f) (Amp g) ≤ dist f g := by
  simpa only [NNReal.coe_one, one_mul] using
    (sixColorProfileAmplitude_lipschitz H N hN beta hbeta).dist_le_mul f g

example (R : ResponseData) (O : BoundedContinuousFunction Joint ℝ) (v : Link → ℝ) :
    Continuous (bcfApproximationMajorant H N hN beta hbeta R O v) :=
  bcfApproximationMajorant_continuous H N hN beta hbeta R O v

example (R : ResponseData) (O : BoundedContinuousFunction Joint ℝ) (v : Link → ℝ) :
    bcfApproximationMajorant H N hN beta hbeta R O v (BCFRep O) =
      OscEnergy (posteriorSixColorVariationProfile H N hN beta hbeta R v) :=
  bcfApproximationMajorant_at_representative H N hN beta hbeta R O v

example (R : ResponseData) (O : BoundedContinuousFunction Joint ℝ)
    (v : Link → ℝ) (hv : ∀ e, 0 ≤ v e)
    (hV : ∀ (B : Cfg) (e : Link) (A C : Cfg),
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorAgreeOff A C e →
        |O (B, A) - O (B, C)| ≤ v e)
    (f : JL2) (epsilon amplitude : ℝ) (hAmplitude : 0 ≤ amplitude)
    (hApprox : ‖f - BCFRep O‖ ≤ epsilon)
    (hEnergy : OscEnergy (posteriorSixColorVariationProfile H N hN beta hbeta R v) ≤
      amplitude ^ 2) : Profile f ≤ (epsilon + amplitude) ^ 2 :=
  sixColorProfileEnergy_le_of_bcfApproximation H N hN beta hbeta
    R O v hv hV f epsilon amplitude hAmplitude hApprox hEnergy

#print axioms GroundStatePosteriorJoint.sixColorResidualOperator_norm_sq
#print axioms GroundStatePosteriorJoint.sixColorResidualOperator_norm_le
#print axioms GroundStatePosteriorJoint.sixColorProfileAmplitude_lipschitz
#print axioms GroundStatePosteriorJoint.bcfApproximationMajorant_continuous
#print axioms GroundStatePosteriorJoint.bcfApproximationMajorant_at_representative
#print axioms GroundStatePosteriorJoint.sixColorProfileEnergy_le_bcfApproximationMajorant
#print axioms GroundStatePosteriorJoint.sixColorProfileEnergy_le_of_bcfApproximation
#print axioms GroundStatePosteriorJoint.sixColorProfileEnergy_le_canonicalBCFApproximationMajorant
#print axioms GroundStatePosteriorJoint.fineFrozenProfileEnergy_le_bcfApproximationMajorant
#print axioms GroundStatePosteriorJoint.fineFrozenProfileEnergy_le_of_bcfApproximation
#print axioms GroundStatePosteriorJoint.fineFrozenProfileEnergy_le_canonicalBCFApproximationMajorant

end

end MGAP4D.MathlibAnalytic
