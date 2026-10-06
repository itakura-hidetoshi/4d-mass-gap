import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointLinkLocalEnergy

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
#check GroundStatePosteriorJoint.jointTransferSignedLinkResidual_sq_integrable
#check GroundStatePosteriorJoint.jointTransferProfileEnergy_le_localEnvelope_add_exterior
#check GroundStatePosteriorJoint.jointTransferProfileEnergy_le_card_of_kernelCancellation
#check GroundStatePosteriorJoint.fineFrozenProfileEnergy_le_localEnvelope_add_exterior

attribute [local instance]
  groundStateJointOneLinkBoundedCoreSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkBoundedCoreSpecialUnitaryCompactSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkBoundedCoreSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitaryBorelSpace
  groundStateJointOneLinkBoundedCoreSpatialLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkUnique

section GeneralCarrier

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "GaugeT" => Matrix.specialUnitaryGroup (Fin N) ℂ
local notation "PairL2" => PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N
local notation "μJ" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure H N hN beta hbeta
local notation "BCFRep" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF H N hN beta hbeta
local notation "P" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2 H N hN beta hbeta
local notation "Obs" => jointTransferBCF H N hN beta hbeta
local notation "Local" => jointTransferLocalEnergyOn H N hN beta hbeta
local notation "Profile" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy H N hN beta hbeta
local notation "NormTransfer" => periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator H N hN beta hbeta

example (x : PairL2) (e : Link) (z : Joint) (g : GaugeT) :
    jointTransferLinkDifference H N hN beta hbeta x e z g =
      Obs x z - Obs x (z.1, Function.update z.2 e g) :=
  jointTransferLinkDifference_eq H N hN beta hbeta x e z g

example (x : PairL2) (e : Link) (z : Joint) :
    jointTransferSignedLinkResidual H N hN beta hbeta x e z =
      Obs x z - posteriorMean H N hN beta hbeta e (fun w => Obs x w) z :=
  jointTransferSignedLinkResidual_eq H N hN beta hbeta x e z

example (x : PairL2) (e : Link) :
    MemLp (jointTransferSignedLinkResidual H N hN beta hbeta x e) 2 μJ :=
  jointTransferSignedLinkResidual_memLp_two H N hN beta hbeta x e

example (x : PairL2) (e : Link) :
    Integrable (fun z => (jointTransferSignedLinkResidual H N hN beta hbeta x e z) ^ 2) μJ :=
  jointTransferSignedLinkResidual_sq_integrable H N hN beta hbeta x e

example (x : PairL2) (e : Link) :
    jointTransferLinkLocalEnergy H N hN beta hbeta x e =
      ‖BCFRep (Obs x) - P e (BCFRep (Obs x))‖ ^ 2 :=
  jointTransferLinkLocalEnergy_eq_initialResidual_sq H N hN beta hbeta x e

example (x : PairL2) : Local x ∅ = 0 :=
  jointTransferLocalEnergyOn_empty H N hN beta hbeta x

example (x : PairL2) (s : Finset Link) : 0 ≤ Local x s :=
  jointTransferLocalEnergyOn_nonneg H N hN beta hbeta x s

example (x : PairL2) :
    Local x Finset.univ = sixColorInitialResidualEnergy H N hN beta hbeta (BCFRep (Obs x)) :=
  jointTransferLocalEnergyOn_univ_eq_initial H N hN beta hbeta x

example (x : PairL2) (s : Finset Link) :
    Local x s + Local x sᶜ =
      sixColorInitialResidualEnergy H N hN beta hbeta (BCFRep (Obs x)) :=
  jointTransferLocalEnergyOn_add_compl H N hN beta hbeta x s

example (x : PairL2) (s t : Finset Link) (hst : s ⊆ t) : Local x s ≤ Local x t :=
  jointTransferLocalEnergyOn_mono H N hN beta hbeta x hst

example (x : PairL2) (s : Finset Link) :
    Local x s ≤ (1 / 6 : ℝ) * (s.card : ℝ) *
      ((kernelRightVariationRate beta) ^ 2 * ‖NormTransfer (pairAbsoluteInput H N x)‖ ^ 2) :=
  jointTransferLocalEnergyOn_le_card_l2Envelope H N hN beta hbeta x s

example (x : PairL2) (s : Finset Link) :
    Profile (BCFRep (Obs x)) ≤ (2 / 3 : ℝ) * (s.card : ℝ) *
      ((kernelRightVariationRate beta) ^ 2 * ‖NormTransfer (pairAbsoluteInput H N x)‖ ^ 2) +
      4 * Local x sᶜ :=
  jointTransferProfileEnergy_le_localEnvelope_add_exterior H N hN beta hbeta x s

end GeneralCarrier

section FrozenFamily

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ) (k : Fin 3)

local notation "Pos" => specialUnitaryTwoWilsonRankPositive
local notation "Orbit" => physicalYangMillsSU2AdjacentFinePairOrbitVector
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "Frozen" => physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "I" => sixColorInitialResidualEnergy (halfExtent (n + 1)) 2 Pos (beta n) (hbeta n)
local notation "Local" => jointTransferLocalEnergyOn (halfExtent (n + 1)) 2 Pos (beta n) (hbeta n)

example : I (Frozen n r k) = Local (Orbit n r k) Finset.univ :=
  fineFrozenInitialEnergy_eq_linkLocal (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k

example : I (Frozen n 0 k) = Local (Orbit n 0 k) Finset.univ :=
  fineFrozenInitialEnergy_eq_linkLocal (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 0 k

end FrozenFamily

#print axioms GroundStatePosteriorJoint.jointTransferLinkDifference_integrable
#print axioms GroundStatePosteriorJoint.jointTransferLinkDifference_eq
#print axioms GroundStatePosteriorJoint.jointTransferLinkDifference_posterior_integrable
#print axioms GroundStatePosteriorJoint.jointTransferSignedLinkResidual_eq
#print axioms GroundStatePosteriorJoint.jointTransferSignedLinkResidual_eq_stage
#print axioms GroundStatePosteriorJoint.jointTransferSignedLinkResidual_memLp_two
#print axioms GroundStatePosteriorJoint.jointTransferSignedLinkResidual_sq_integrable
#print axioms GroundStatePosteriorJoint.jointTransferLinkLocalEnergy_eq_initialResidual_sq
#print axioms GroundStatePosteriorJoint.jointTransferLinkLocalEnergy_nonneg
#print axioms GroundStatePosteriorJoint.jointTransferLinkLocalEnergy_eq_zero_of_ae_kernelCancellation
#print axioms GroundStatePosteriorJoint.jointTransferLocalEnergyOn_empty
#print axioms GroundStatePosteriorJoint.jointTransferLocalEnergyOn_nonneg
#print axioms GroundStatePosteriorJoint.jointTransferLocalEnergyOn_univ_eq_initial
#print axioms GroundStatePosteriorJoint.jointTransferLocalEnergyOn_add_compl
#print axioms GroundStatePosteriorJoint.jointTransferLocalEnergyOn_mono
#print axioms GroundStatePosteriorJoint.jointTransferLocalEnergyOn_le_card_l2Envelope
#print axioms GroundStatePosteriorJoint.jointTransferProfileEnergy_le_localEnvelope_add_exterior
#print axioms GroundStatePosteriorJoint.jointTransferProfileEnergy_le_card_of_kernelCancellation
#print axioms GroundStatePosteriorJoint.fineFrozenInitialEnergy_eq_linkLocal
#print axioms GroundStatePosteriorJoint.fineFrozenProfileEnergy_le_localEnvelope_add_exterior

end

end MGAP4D.MathlibAnalytic
