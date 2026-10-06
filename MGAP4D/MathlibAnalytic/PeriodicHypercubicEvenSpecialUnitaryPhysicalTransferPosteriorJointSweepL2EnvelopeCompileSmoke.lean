import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointSweepL2Envelope

/-! Regression contracts on unchanged chronological sweeps and genuine joint carriers. -/
namespace MGAP4D.MathlibAnalytic

open MeasureTheory GroundStatePosteriorJoint
open scoped InnerProductSpace InnerProduct BigOperators

noncomputable section

#check realHilbertProjectionSweep_pathLoss_le_four_initial
#check realHilbertProjectionSweep_displacement_sq_le_initial
#check GroundStatePosteriorJoint.sixColorProfileEnergy_le_four_initialResidualEnergy
#check GroundStatePosteriorJoint.jointTransferProfileEnergy_le_l2Envelope
#check GroundStatePosteriorJoint.fineFrozenProfileEnergy_le_l2Envelope
#check realHilbertProjectionSweep_pathLoss_add_two_displacement_sq_le_four_initial
#check realHilbertProjectionSweep_stageResidual_sq_le_four_initial
#check GroundStatePosteriorJoint.jointTransferStageEnergy_le_l2Envelope
#check GroundStatePosteriorJoint.sixColorInitialResidualEnergy_continuous
#check GroundStatePosteriorJoint.fineFrozenProfileEnergy_eq_zero_without_responseData

section AbstractExamples

variable {E C : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (P : C → E →L[ℝ] E) (hIdem : ∀ c, (P c).comp (P c) = P c)
variable (hSymm : ∀ c (x y : E), inner ℝ (P c x) y = inner ℝ x (P c y))

example (x : E) : realHilbertProjectionSweepPathLoss P [] x = 0 := rfl

example (cs : List C) (x y : E) :
    realHilbertProjectionSweepPathLoss P cs y + 2 * ‖x - realHilbertProjectionSweep P cs y‖ ^ 2 ≤
      2 * ‖x - y‖ ^ 2 + 4 * (cs.map fun c => ‖x - P c x‖ ^ 2).sum :=
  realHilbertProjectionSweep_union_potential P hIdem hSymm cs x y

example (cs : List C) (x : E) : realHilbertProjectionSweepPathLoss P cs x ≤
    4 * (cs.map fun c => ‖x - P c x‖ ^ 2).sum :=
  realHilbertProjectionSweep_pathLoss_le_four_initial P hIdem hSymm cs x

example (cs : List C) (x : E) : ‖x - realHilbertProjectionSweep P cs x‖ ^ 2 ≤
    (cs.map fun c => ‖x - P c x‖ ^ 2).sum :=
  realHilbertProjectionSweep_displacement_sq_le_initial P hIdem hSymm cs x

example (c : C) (x : E) : realHilbertProjectionSweepPathLoss P [c, c] x ≤ 8 * ‖x - P c x‖ ^ 2 := by
  have h := realHilbertProjectionSweep_pathLoss_le_four_initial P hIdem hSymm [c, c] x
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
  linarith

example (pre : List C) (e : C) (x : E) :
    ‖realHilbertProjectionSweep P pre x - P e (realHilbertProjectionSweep P pre x)‖ ^ 2 ≤
      4 * ((pre ++ [e]).map fun c => ‖x - P c x‖ ^ 2).sum :=
  realHilbertProjectionSweep_stageResidual_sq_le_four_initial P hIdem hSymm pre e x

end AbstractExamples

attribute [local instance]
  groundStateJointOneLinkBoundedCoreSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkBoundedCoreSpecialUnitaryCompactSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkBoundedCoreSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitaryBorelSpace
  groundStateJointOneLinkBoundedCoreSpatialLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkUnique

section ConcreteExamples

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "JL2" => PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta
local notation "PairL2" => PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N
local notation "PJoint" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2 H N hN beta hbeta
local notation "BCFRep" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF H N hN beta hbeta
local notation "Profile" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy H N hN beta hbeta
local notation "Initial" => sixColorInitialResidualEnergy H N hN beta hbeta
local notation "S" => periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator H N hN beta hbeta
local notation "Obs" => jointTransferBCF H N hN beta hbeta
local notation "Rate" => kernelRightVariationRate beta

example (f : JL2) : 0 ≤ Initial f := sixColorInitialResidualEnergy_nonneg H N hN beta hbeta f

example : Continuous Initial := sixColorInitialResidualEnergy_continuous H N hN beta hbeta

example (f : JL2) : Profile f ≤ 4 * Initial f :=
  sixColorProfileEnergy_le_four_initialResidualEnergy H N hN beta hbeta f

example (f : JL2) : Profile f ≤ min (‖posteriorLeftCenteredOperator H N hN beta hbeta f‖ ^ 2) (4 * Initial f) :=
  sixColorProfileEnergy_le_min_centered_initial H N hN beta hbeta f

example (pre : List Link) (e : Link) (F : BoundedContinuousFunction Joint ℝ) :
    posteriorStageResidualEnergy H N hN beta hbeta pre e F =
      ‖realHilbertProjectionSweep PJoint pre (BCFRep F) - PJoint e (realHilbertProjectionSweep PJoint pre (BCFRep F))‖ ^ 2 :=
  posteriorStageEnergy_eq_bcfResidualNormSq H N hN beta hbeta pre e F

example (x : PairL2) (e : Link) : ‖BCFRep (Obs x) - PJoint e (BCFRep (Obs x))‖ ^ 2 ≤
    Rate ^ 2 * ‖S (pairAbsoluteInput H N x)‖ ^ 2 :=
  jointTransferInitialResidual_sq_le_l2Envelope H N hN beta hbeta x e

example (x : PairL2) (pre : List Link) (e : Link) :
    posteriorStageResidualEnergy H N hN beta hbeta pre e (Obs x) ≤
      4 * ((pre.length : ℝ) + 1) * (Rate ^ 2 * ‖S (pairAbsoluteInput H N x)‖ ^ 2) :=
  jointTransferStageEnergy_le_l2Envelope H N hN beta hbeta x pre e

example (x : PairL2) : Profile (BCFRep (Obs x)) ≤
    (2 / 3 : ℝ) * (Fintype.card Link : ℝ) * (Rate ^ 2 * ‖S (pairAbsoluteInput H N x)‖ ^ 2) :=
  jointTransferProfileEnergy_le_l2Envelope H N hN beta hbeta x

end ConcreteExamples

section FrozenExamples

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ) (k : Fin 3)

example (hzero : beta n = 0) :
    physicalYangMillsSU2AdjacentFineGroundStateSweepStageProfileEnergy
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k = 0 :=
  fineFrozenProfileEnergy_eq_zero_without_responseData n r k hzero

example (hzero : beta n = 0) :
    physicalYangMillsSU2AdjacentFineGroundStateSweepStageProfileEnergy
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 0 k = 0 :=
  fineFrozenProfileEnergy_eq_zero_without_responseData n 0 k hzero

end FrozenExamples

#print axioms realHilbertProjection_reference_distance_sq
#print axioms realHilbertProjection_union_potential_step
#print axioms realHilbertProjectionSweep_union_potential
#print axioms realHilbertProjectionSweep_pathLoss_add_two_displacement_sq_le_four_initial
#print axioms realHilbertProjectionSweep_pathLoss_le_four_initial
#print axioms realHilbertProjectionSweep_displacement_sq_le_initial
#print axioms realHilbertProjectionSweep_stageResidual_sq_le_four_initial
#print axioms GroundStatePosteriorJoint.sixColorInitialResidualEnergy_continuous
#print axioms GroundStatePosteriorJoint.posteriorLink_sum_eq_colorFiber_sum
#print axioms GroundStatePosteriorJoint.fixedColorPathLoss_le_four_initial
#print axioms GroundStatePosteriorJoint.sixColorProfileEnergy_le_four_initialResidualEnergy
#print axioms GroundStatePosteriorJoint.sixColorProfileEnergy_le_min_centered_initial
#print axioms GroundStatePosteriorJoint.posteriorStageEnergy_eq_bcfResidualNormSq
#print axioms GroundStatePosteriorJoint.jointTransferInitialResidual_sq_le_l2Envelope
#print axioms GroundStatePosteriorJoint.jointTransferStageEnergy_le_l2Envelope
#print axioms GroundStatePosteriorJoint.jointTransferProfileEnergy_le_l2Envelope
#print axioms GroundStatePosteriorJoint.fineFrozenProfileEnergy_le_l2Envelope
#print axioms GroundStatePosteriorJoint.fineFrozenProfileEnergy_eq_zero_without_responseData

end

end MGAP4D.MathlibAnalytic
