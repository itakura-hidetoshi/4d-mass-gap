import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointSourceLocalTilt

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

namespace SourceLocalTiltSmoke

section General

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "GaugeT" => Matrix.specialUnitaryGroup (Fin N) ℂ
local notation "μP" => periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
local notation "μJ" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure H N hN beta hbeta
local notation "Nu" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure H N hN beta hbeta
local notation "PairL2" => PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N
local notation "J" => jointTransferKernel H N hN beta hbeta
local notation "Obs" => jointTransferBCF H N hN beta hbeta
local notation "Out" => outputRightLinkTilt H N hN beta hbeta
local notation "Resp" => sourceLinkResponse H N hN beta hbeta
local notation "Diff" => jointTransferLinkDifference H N hN beta hbeta

 theorem unchangedValue (u a : GaugeT) : sourceRightLinkTilt N beta u a a = 1 :=
  sourceRightLinkTilt_current N beta u a

 theorem zeroCoupling (u a g : GaugeT) : sourceRightLinkTilt N 0 u a g = 1 :=
  sourceRightLinkTilt_beta_zero N u a g

 theorem consecutiveValues (u a g h : GaugeT) :
    sourceRightLinkTilt N beta u a g * sourceRightLinkTilt N beta u g h =
      sourceRightLinkTilt N beta u a h :=
  sourceRightLinkTilt_cocycle N beta u a g h

include hN hbeta in
 theorem sourceMultiplierWidth (u a g : GaugeT) :
    |sourceRightLinkTilt N beta u a g - 1| ≤ Real.exp (2 * beta) - 1 :=
  sourceRightLinkTilt_sub_one_abs_le N hN beta hbeta u a g

 theorem exactKernelFactor (y z : Joint) (e : Link) (g : GaugeT) :
    J y (z.1, Function.update z.2 e g) =
      Out z e g * sourceRightLinkTilt N beta (y.2 e) (z.2 e) g * J y z :=
  jointTransferKernel_right_update_eq_sourceTilt H N hN beta hbeta y z e g

 theorem sameSourceLink (y v z : Joint) (e : Link) (g : GaugeT) (hlink : y.2 e = v.2 e) :
    J y (z.1, Function.update z.2 e g) * J v z =
      J v (z.1, Function.update z.2 e g) * J y z :=
  jointTransferKernel_update_cross_eq_of_sourceLink_eq H N hN beta hbeta y v z e g hlink

 theorem signedIntegral (x : PairL2) (e : Link) (z : Joint) (g : GaugeT) :
    Integrable (fun y => J y z *
      (sourceRightLinkTilt N beta (y.2 e) (z.2 e) g - 1) * x y) μP :=
  sourceLinkResponse_integrable H N hN beta hbeta x e z g

 theorem signedEnvelope (x : PairL2) (e : Link) (z : Joint) (g : GaugeT) :
    |Resp x e z g| ≤ (Real.exp (2 * beta) - 1) * jointTransferEnvelope H N hN beta hbeta x z :=
  sourceLinkResponse_abs_le_envelope H N hN beta hbeta x e z g

 theorem signedDriftResponse (x : PairL2) (e : Link) (z : Joint) (g : GaugeT) :
    Diff x e z g = (1 - Out z e g) * Obs x z - Out z e g * Resp x e z g :=
  jointTransferLinkDifference_eq_sourceTilt H N hN beta hbeta x e z g

 theorem commonDriftCancellation (x v : PairL2) (e : Link) (z : Joint) (g : GaugeT) :
    Obs v z * Diff x e z g - Obs x z * Diff v e z g =
      Out z e g * (Obs x z * Resp v e z g - Obs v z * Resp x e z g) :=
  jointTransferSourceContrast_eq H N hN beta hbeta x v e z g

 theorem zeroCouplingResponse (x : PairL2) (e : Link) (z : Joint) (g : GaugeT) :
    sourceLinkResponse H N hN 0 (by norm_num) x e z g = 0 := by
  simp [sourceLinkResponse, sourceRightLinkTilt]

 theorem posteriorSquare (x : PairL2) (e : Link) (z : Joint) :
    Integrable (fun g => ((1 - Out z e g) * Obs x z - Out z e g * Resp x e z g) ^ 2)
      (Nu z.1 z.2 e) :=
  sourceTiltDefect_sq_posterior_integrable H N hN beta hbeta x e z

 theorem jointSquare (x : PairL2) (e : Link) :
    Integrable (fun z => ∫ g,
      ((1 - Out z e g) * Obs x z - Out z e g * Resp x e z g) ^ 2 ∂Nu z.1 z.2 e) μJ :=
  sourceTiltDefect_sq_joint_integrable H N hN beta hbeta x e

 theorem originalEnergy (x : PairL2) (e : Link) :
    jointTransferLinkLocalEnergy H N hN beta hbeta x e =
      (1 / 2 : ℝ) * ∫ z, ∫ g,
        ((1 - Out z e g) * Obs x z - Out z e g * Resp x e z g) ^ 2 ∂Nu z.1 z.2 e ∂μJ := by
  have h := jointTransferLinkResamplingEnergy_eq_twice_localEnergy H N hN beta hbeta x e
  rw [jointTransferLinkResamplingEnergy_eq_sourceTilt] at h
  linarith

end General

section Frozen

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ) (k : Fin 3)
local notation "Hn" => halfExtent (n + 1)
local notation "Pos" => specialUnitaryTwoWilsonRankPositive
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "μJ" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure Hn 2 Pos (beta n) (hbeta n)
local notation "Nu" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure Hn 2 Pos (beta n) (hbeta n)
local notation "Orbit0" => physicalYangMillsSU2AdjacentFinePairOrbitVector
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 0 k
local notation "Frozen0" => physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 0 k
local notation "Obs" => jointTransferBCF Hn 2 Pos (beta n) (hbeta n)
local notation "Out" => outputRightLinkTilt Hn 2 Pos (beta n) (hbeta n)
local notation "Resp" => sourceLinkResponse Hn 2 Pos (beta n) (hbeta n)

 theorem actualFrozenZeroStep :
    sixColorInitialResidualEnergy Hn 2 Pos (beta n) (hbeta n) Frozen0 =
      (1 / 12 : ℝ) * ∑ e : Link, ∫ z, ∫ g,
        ((1 - Out z e g) * Obs Orbit0 z - Out z e g * Resp Orbit0 e z g) ^ 2
          ∂Nu z.1 z.2 e ∂μJ :=
  fineFrozenInitialEnergy_eq_sourceTilt n 0 k

end Frozen

end SourceLocalTiltSmoke

#check GroundStatePosteriorJoint.sourceRightLinkTilt_sub_one_abs_le
#check GroundStatePosteriorJoint.jointTransferKernel_right_update_eq_sourceTilt
#check GroundStatePosteriorJoint.jointTransferKernel_update_cross_eq_of_sourceLink_eq
#check GroundStatePosteriorJoint.sourceLinkResponse_integrable
#check GroundStatePosteriorJoint.sourceLinkResponse_abs_le_envelope
#check GroundStatePosteriorJoint.jointTransferLinkDifference_eq_sourceTilt
#check GroundStatePosteriorJoint.jointTransferSourceContrast_eq
#check GroundStatePosteriorJoint.fineFrozenInitialEnergy_eq_sourceTilt

#print axioms GroundStatePosteriorJoint.sourceRightLinkTilt_pos
#print axioms GroundStatePosteriorJoint.sourceRightLinkTilt_current
#print axioms GroundStatePosteriorJoint.sourceRightLinkTilt_beta_zero
#print axioms GroundStatePosteriorJoint.sourceRightLinkTilt_cocycle
#print axioms GroundStatePosteriorJoint.sourceRightLinkTilt_sub_one_abs_le
#print axioms GroundStatePosteriorJoint.crossingAction_right_update_sub
#print axioms GroundStatePosteriorJoint.oneSlabKernel_right_update_eq_sourceTilt
#print axioms GroundStatePosteriorJoint.outputRightLinkTilt_pos
#print axioms GroundStatePosteriorJoint.jointTransferKernel_right_update_eq_sourceTilt
#print axioms GroundStatePosteriorJoint.jointTransferKernel_update_cross_eq_of_sourceLink_eq
#print axioms GroundStatePosteriorJoint.sourceLinkResponse_integrable
#print axioms GroundStatePosteriorJoint.sourceLinkResponse_eq
#print axioms GroundStatePosteriorJoint.sourceLinkResponse_abs_le_envelope
#print axioms GroundStatePosteriorJoint.jointTransferLinkDifference_eq_sourceTilt
#print axioms GroundStatePosteriorJoint.jointTransferSourceContrast_eq
#print axioms GroundStatePosteriorJoint.sourceTiltDefect_sq_posterior_integrable
#print axioms GroundStatePosteriorJoint.sourceTiltDefect_sq_joint_integrable
#print axioms GroundStatePosteriorJoint.jointTransferLinkResamplingEnergy_eq_sourceTilt
#print axioms GroundStatePosteriorJoint.fineFrozenInitialEnergy_eq_sourceTilt
#print axioms SourceLocalTiltSmoke.unchangedValue
#print axioms SourceLocalTiltSmoke.zeroCoupling
#print axioms SourceLocalTiltSmoke.consecutiveValues
#print axioms SourceLocalTiltSmoke.sourceMultiplierWidth
#print axioms SourceLocalTiltSmoke.exactKernelFactor
#print axioms SourceLocalTiltSmoke.sameSourceLink
#print axioms SourceLocalTiltSmoke.signedIntegral
#print axioms SourceLocalTiltSmoke.signedEnvelope
#print axioms SourceLocalTiltSmoke.signedDriftResponse
#print axioms SourceLocalTiltSmoke.commonDriftCancellation
#print axioms SourceLocalTiltSmoke.zeroCouplingResponse
#print axioms SourceLocalTiltSmoke.posteriorSquare
#print axioms SourceLocalTiltSmoke.jointSquare
#print axioms SourceLocalTiltSmoke.originalEnergy
#print axioms SourceLocalTiltSmoke.actualFrozenZeroStep

end

end MGAP4D.MathlibAnalytic
