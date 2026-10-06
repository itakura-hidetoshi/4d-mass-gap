import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointResamplingDirichlet

/-! Regression contracts for exact resampling factors and unchanged carriers.

Carrier-valued binders are declared on each named regression theorem rather
than reused through anonymous private examples. Every regression proof itself
is axiom-printed, in addition to all nineteen mathematical interface theorems.
-/

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
  groundStateJointOneLinkBoundedCoreTargetLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkUnique

namespace PosteriorResamplingDirichletSmoke

section General

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "μJ" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure H N hN beta hbeta
local notation "Nu" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure H N hN beta hbeta
local notation "PairL2" => PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N
local notation "BCFRep" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF H N hN beta hbeta
local notation "PJoint" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2 H N hN beta hbeta
local notation "Obs" => jointTransferBCF H N hN beta hbeta
local notation "Local" => jointTransferLocalEnergyOn H N hN beta hbeta
local notation "B" => jointTransferLinkLocalEnergy H N hN beta hbeta
local notation "Q" => jointTransferLinkResamplingEnergy H N hN beta hbeta
local notation "T" => periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator H N hN beta hbeta

theorem stationarity (e : Link) (G : Joint → ℝ) (hG : StronglyMeasurable G)
    (c : ℝ) (hc : ∀ z, ‖G z‖ ≤ c) :
    (∫ z, posteriorMean H N hN beta hbeta e G z ∂μJ) = ∫ z, G z ∂μJ :=
  posteriorMean_integral_eq H N hN beta hbeta e G hG c hc

theorem outerIntegrable (e : Link) (F : BoundedContinuousFunction Joint ℝ) :
    Integrable (posteriorResamplingSquare H N hN beta hbeta e F) μJ :=
  posteriorResamplingSquare_integrable H N hN beta hbeta e F

theorem projectionHalf (e : Link) (F : BoundedContinuousFunction Joint ℝ) :
    ‖BCFRep F - PJoint e (BCFRep F)‖ ^ 2 =
      (1 / 2 : ℝ) * posteriorResamplingEnergy H N hN beta hbeta e F :=
  posteriorInitialResidual_sq_eq_half_resampling H N hN beta hbeta e F

theorem signedInnerIntegrable (x : PairL2) (e : Link) (z : Joint) :
    Integrable (fun g => jointTransferLinkDifference H N hN beta hbeta x e z g ^ 2)
      (Nu z.1 z.2 e) :=
  jointTransferLinkDifference_sq_posterior_integrable H N hN beta hbeta x e z

theorem signedOuterIntegrable (x : PairL2) (e : Link) :
    Integrable (fun z => ∫ g,
      jointTransferLinkDifference H N hN beta hbeta x e z g ^ 2 ∂Nu z.1 z.2 e) μJ :=
  jointTransferLinkResamplingSquare_integrable H N hN beta hbeta x e

theorem signedTwice (x : PairL2) (e : Link) : Q x e = 2 * B x e :=
  jointTransferLinkResamplingEnergy_eq_twice_localEnergy H N hN beta hbeta x e

theorem signedHalf (x : PairL2) (e : Link) : B x e = (1 / 2 : ℝ) * Q x e := by
  have h := jointTransferLinkResamplingEnergy_eq_twice_localEnergy H N hN beta hbeta x e
  linarith

theorem finiteSet (x : PairL2) (s : Finset Link) :
    Local x s = (1 / 12 : ℝ) * ∑ t ∈ s, Q x t :=
  jointTransferLocalEnergyOn_eq_resampling H N hN beta hbeta x s

theorem emptySet (x : PairL2) : (1 / 12 : ℝ) * ∑ t ∈ (∅ : Finset Link), Q x t = 0 := by
  simp

theorem singleton (x : PairL2) (e : Link) : Local x {e} = (1 / 12 : ℝ) * Q x e := by
  simpa using jointTransferLocalEnergyOn_eq_resampling H N hN beta hbeta x {e}

theorem fullSet (x : PairL2) :
    sixColorInitialResidualEnergy H N hN beta hbeta (BCFRep (Obs x)) =
      (1 / 12 : ℝ) * ∑ t : Link, Q x t := by
  rw [← jointTransferLocalEnergyOn_univ_eq_initial, jointTransferLocalEnergyOn_eq_resampling]

theorem halfEnvelope (x : PairL2) (e : Link) : B x e ≤ (1 / 2 : ℝ) *
    ((kernelRightVariationRate beta) ^ 2 * ‖T (pairAbsoluteInput H N x)‖ ^ 2) :=
  jointTransferLinkLocalEnergy_le_half_l2Envelope H N hN beta hbeta x e

theorem nearExterior (x : PairL2) (s : Finset Link) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy
      H N hN beta hbeta (BCFRep (Obs x)) ≤ (1 / 3 : ℝ) * (s.card : ℝ) *
        ((kernelRightVariationRate beta) ^ 2 * ‖T (pairAbsoluteInput H N x)‖ ^ 2) + 4 * Local x sᶜ :=
  jointTransferProfileEnergy_le_half_localEnvelope_add_exterior H N hN beta hbeta x s

theorem zeroCoupling (x : PairL2) (e : Link) :
    jointTransferLinkResamplingEnergy H N hN 0 (by norm_num) x e = 0 := by
  have h := jointTransferLinkLocalEnergy_le_half_l2Envelope H N hN 0 (by norm_num) x e
  have hn := jointTransferLinkLocalEnergy_nonneg H N hN 0 (by norm_num) x e
  have h0 : jointTransferLinkLocalEnergy H N hN 0 (by norm_num) x e ≤ 0 := by
    simpa [kernelRightVariationRate] using h
  have hz := le_antisymm h0 hn
  rw [jointTransferLinkResamplingEnergy_eq_twice_localEnergy, hz, mul_zero]

end General

section Frozen

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ) (k : Fin 3)

theorem frozenFamily :
    sixColorInitialResidualEnergy (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
      (beta n) (hbeta n)
      (physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k) =
      (1 / 12 : ℝ) * ∑ e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)),
        jointTransferLinkResamplingEnergy (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n)
          (physicalYangMillsSU2AdjacentFinePairOrbitVector
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k) e :=
  fineFrozenInitialEnergy_eq_resampling n r k

theorem frozenZeroIterate :
    sixColorInitialResidualEnergy (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
      (beta n) (hbeta n)
      (physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 0 k) =
      (1 / 12 : ℝ) * ∑ e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)),
        jointTransferLinkResamplingEnergy (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n)
          (physicalYangMillsSU2AdjacentFinePairOrbitVector
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 0 k) e :=
  fineFrozenInitialEnergy_eq_resampling n 0 k

end Frozen

#check GroundStatePosteriorJoint.posteriorMean_integral_eq
#check GroundStatePosteriorJoint.posteriorResamplingSquare_integrable
#check GroundStatePosteriorJoint.posteriorResamplingEnergy_eq_twice_stageEnergy
#check GroundStatePosteriorJoint.posteriorInitialResidual_sq_eq_half_resampling
#check GroundStatePosteriorJoint.jointTransferLinkResamplingEnergy_eq_twice_localEnergy
#check GroundStatePosteriorJoint.jointTransferLocalEnergyOn_eq_resampling
#check GroundStatePosteriorJoint.jointTransferLinkLocalEnergy_le_half_l2Envelope
#check GroundStatePosteriorJoint.fineFrozenInitialEnergy_eq_resampling
#check GroundStatePosteriorJoint.fineFrozenProfileEnergy_le_half_localEnvelope_add_exterior
#check GroundStatePosteriorJoint.fineFrozenProfileEnergy_le_half_l2Envelope

#print axioms GroundStatePosteriorJoint.posteriorMean_integral_eq
#print axioms GroundStatePosteriorJoint.posteriorResamplingDifferenceSquare_integrable
#print axioms GroundStatePosteriorJoint.posteriorResamplingSquare_nonneg
#print axioms GroundStatePosteriorJoint.posteriorResamplingSquare_formula
#print axioms GroundStatePosteriorJoint.posteriorResamplingSquare_integrable
#print axioms GroundStatePosteriorJoint.posteriorResamplingEnergy_eq_twice_stageEnergy
#print axioms GroundStatePosteriorJoint.posteriorInitialResidual_sq_eq_half_resampling
#print axioms GroundStatePosteriorJoint.jointTransferLinkDifference_sq_posterior_integrable
#print axioms GroundStatePosteriorJoint.jointTransferLinkResamplingSquare_integrable
#print axioms GroundStatePosteriorJoint.jointTransferLinkResamplingEnergy_eq
#print axioms GroundStatePosteriorJoint.jointTransferLinkResamplingEnergy_eq_twice_localEnergy
#print axioms GroundStatePosteriorJoint.jointTransferLocalEnergyOn_eq_resampling
#print axioms GroundStatePosteriorJoint.jointTransferLinkLocalEnergy_le_half_l2Envelope
#print axioms GroundStatePosteriorJoint.jointTransferLocalEnergyOn_le_card_half_l2Envelope
#print axioms GroundStatePosteriorJoint.jointTransferProfileEnergy_le_half_localEnvelope_add_exterior
#print axioms GroundStatePosteriorJoint.jointTransferProfileEnergy_le_half_l2Envelope
#print axioms GroundStatePosteriorJoint.fineFrozenInitialEnergy_eq_resampling
#print axioms GroundStatePosteriorJoint.fineFrozenProfileEnergy_le_half_localEnvelope_add_exterior
#print axioms GroundStatePosteriorJoint.fineFrozenProfileEnergy_le_half_l2Envelope

#print axioms stationarity
#print axioms outerIntegrable
#print axioms projectionHalf
#print axioms signedInnerIntegrable
#print axioms signedOuterIntegrable
#print axioms signedTwice
#print axioms signedHalf
#print axioms finiteSet
#print axioms emptySet
#print axioms singleton
#print axioms fullSet
#print axioms halfEnvelope
#print axioms nearExterior
#print axioms zeroCoupling
#print axioms frozenFamily
#print axioms frozenZeroIterate

end PosteriorResamplingDirichletSmoke

end

end MGAP4D.MathlibAnalytic
