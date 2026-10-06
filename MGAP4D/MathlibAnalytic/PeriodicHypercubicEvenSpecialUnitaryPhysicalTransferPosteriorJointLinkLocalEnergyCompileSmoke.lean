import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointSweepL2Envelope

/-! Regression contracts for the link-resolved signed kernel construction. -/
namespace MGAP4D.MathlibAnalytic

open MeasureTheory GroundStatePosteriorJoint
open scoped BigOperators

noncomputable section

#check GroundStatePosteriorJoint.jointTransferLinkDifference_eq
#check GroundStatePosteriorJoint.jointTransferSignedLinkResidual_eq
#check GroundStatePosteriorJoint.jointTransferLinkLocalEnergy_eq_initialResidual_sq
#check GroundStatePosteriorJoint.jointTransferLocalEnergyOn_univ_eq_initial
#check GroundStatePosteriorJoint.jointTransferLocalEnergyOn_add_compl
#check GroundStatePosteriorJoint.fineFrozenInitialEnergy_eq_linkLocal

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
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "PairL2" => PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N
local notation "BCFRep" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF H N hN beta hbeta
local notation "P" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2 H N hN beta hbeta
local notation "Obs" => jointTransferBCF H N hN beta hbeta
local notation "Local" => jointTransferLocalEnergyOn H N hN beta hbeta

example (x : PairL2) (e : Link) :
    jointTransferLinkLocalEnergy H N hN beta hbeta x e =
      ‖BCFRep (Obs x) - P e (BCFRep (Obs x))‖ ^ 2 :=
  jointTransferLinkLocalEnergy_eq_initialResidual_sq H N hN beta hbeta x e

example (x : PairL2) : Local x ∅ = 0 :=
  jointTransferLocalEnergyOn_empty H N hN beta hbeta x

example (x : PairL2) (s : Finset Link) : 0 ≤ Local x s :=
  jointTransferLocalEnergyOn_nonneg H N hN beta hbeta x s

example (x : PairL2) (s : Finset Link) :
    Local x s + Local x sᶜ =
      sixColorInitialResidualEnergy H N hN beta hbeta (BCFRep (Obs x)) :=
  jointTransferLocalEnergyOn_add_compl H N hN beta hbeta x s

end

end MGAP4D.MathlibAnalytic
