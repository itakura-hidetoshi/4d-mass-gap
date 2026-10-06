import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentRightVariation

/-! Regression contracts on the unchanged carriers and actual frozen family. -/
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

#check GroundStatePosteriorJoint.continuousJointSqrtDensity_right_harnack
#check GroundStatePosteriorJoint.jointTransferKernel_right_harnack
#check GroundStatePosteriorJoint.jointTransferBCF_right_variation
#check GroundStatePosteriorJoint.jointTransferEnvelope_rep_norm
#check GroundStatePosteriorJoint.fineFrozenProfileEnergy_le_kernelVariationEnergy
#check GroundStatePosteriorJoint.jointTransferKernel_right_difference
#check GroundStatePosteriorJoint.jointTransferPosteriorResidualEnergy_le
#check GroundStatePosteriorJoint.fineFrozenPosteriorResidualEnergy_le
#check GroundStatePosteriorJoint.fineFrozenProfileEnergy_le_canonicalKernelVariationEnergy
#check GroundStatePosteriorJoint.fineFrozenKernelInitialVariation_eq_zero

example : kernelRightVariationRate 0 = 0 := kernelRightVariationRate_zero

section GeneralExamples

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "GaugeT" => Matrix.specialUnitaryGroup (Fin N) ℂ
local notation "PairL2" => PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N
local notation "BCFRep" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF H N hN beta hbeta
local notation "Kernel" => jointTransferKernel H N hN beta hbeta
local notation "Obs" => jointTransferBCF H N hN beta hbeta
local notation "Envelope" => jointTransferEnvelope H N hN beta hbeta
local notation "Rate" => kernelRightVariationRate beta

example : 0 ≤ Rate := kernelRightVariationRate_nonneg beta hbeta

example (x z : Joint) : 0 ≤ Kernel x z := jointTransferKernel_nonneg H N hN beta hbeta x z

example (B A : Cfg) (e : Link) (g h : GaugeT) :
    continuousJointSqrtDensity H N hN beta hbeta (B, Function.update A e g) ≤
      Real.exp (8 * beta) * continuousJointSqrtDensity H N hN beta hbeta (B, Function.update A e h) :=
  continuousJointSqrtDensity_right_harnack H N hN beta hbeta B A e g h

example (x : Joint) (B A : Cfg) (e : Link) (g h : GaugeT) :
    Kernel x (B, Function.update A e g) ≤ Real.exp (16 * beta) * Kernel x (B, Function.update A e h) :=
  jointTransferKernel_right_harnack H N hN beta hbeta x B A e g h

example (x : Joint) (B A : Cfg) (e : Link) (g h : GaugeT) :
    |Kernel x (B, Function.update A e g) - Kernel x (B, Function.update A e h)| ≤
      Rate * Kernel x (B, Function.update A e g) :=
  jointTransferKernel_right_difference H N hN beta hbeta x B A e g h

example (f : PairL2) (z : Joint) : 0 ≤ Envelope f z :=
  jointTransferEnvelope_nonneg H N hN beta hbeta f z

example (f : PairL2) :
    ‖BCFRep (Envelope f)‖ = ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
      H N hN beta hbeta (pairAbsoluteInput H N f)‖ :=
  jointTransferEnvelope_rep_norm H N hN beta hbeta f

example (f : PairL2) (B : Cfg) (e : Link) (A C : Cfg)
    (h : PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorAgreeOff A C e) :
    |Obs f (B, A) - Obs f (B, C)| ≤ Rate * Envelope f (B, A) :=
  jointTransferBCF_right_variation H N hN beta hbeta f B e A C h

example (f : PairL2) (B : Cfg) (e : Link) (A C : Cfg)
    (h : PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorAgreeOff A C e) :
    |Obs f (B, A) - Obs f (B, C)| ≤ kernelRightInitialVariation H N hN beta hbeta f e :=
  kernelRightInitialVariation_bound H N hN beta hbeta f B e A C h

example (f : PairL2) (e : Link) (z : Joint) :
    |Obs f z - posteriorMean H N hN beta hbeta e (Obs f) z| ≤ Rate * Envelope f z :=
  jointTransferPosteriorResidual_abs_le_envelope H N hN beta hbeta f e z

example (f : PairL2) (e : Link) :
    posteriorStageResidualEnergy H N hN beta hbeta [] e (Obs f) ≤
      Rate ^ 2 * ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        H N hN beta hbeta (pairAbsoluteInput H N f)‖ ^ 2 :=
  jointTransferPosteriorResidualEnergy_le H N hN beta hbeta f e

end GeneralExamples

section FrozenExamples

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ) (k : Fin 3)

example (hzero : beta n = 0) :
    fineFrozenKernelInitialVariation (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k =
      (fun _ => 0) := fineFrozenKernelInitialVariation_eq_zero n r k hzero

example (R : PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteExpectationResponseMatrixData
    (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)) :
    physicalYangMillsSU2AdjacentFineGroundStateSweepStageProfileEnergy
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k ≤
    periodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageOscillationEnergy (halfExtent (n + 1))
      (posteriorSixColorVariationProfile (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n) R
        (fineFrozenKernelInitialVariation (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k)) :=
  fineFrozenProfileEnergy_le_kernelVariationEnergy n r k R

end FrozenExamples

#print axioms GroundStatePosteriorJoint.kernelRightVariationRate_nonneg
#print axioms GroundStatePosteriorJoint.continuousJointSqrtDensity_right_harnack
#print axioms GroundStatePosteriorJoint.jointTransferKernel_right_harnack
#print axioms GroundStatePosteriorJoint.jointTransferKernel_right_difference
#print axioms GroundStatePosteriorJoint.jointTransferBCF_eq_integral_kernel
#print axioms GroundStatePosteriorJoint.pairAbsoluteInput_ae_eq
#print axioms GroundStatePosteriorJoint.jointTransferEnvelope_eq_integral
#print axioms GroundStatePosteriorJoint.jointTransferEnvelope_nonneg
#print axioms GroundStatePosteriorJoint.jointTransferEnvelope_rep_norm
#print axioms GroundStatePosteriorJoint.jointTransferBCF_right_variation
#print axioms GroundStatePosteriorJoint.kernelRightInitialVariation_bound
#print axioms GroundStatePosteriorJoint.jointTransferPosteriorResidual_abs_le_envelope
#print axioms GroundStatePosteriorJoint.jointTransferPosteriorResidualEnergy_le
#print axioms GroundStatePosteriorJoint.fineFrozenBCF_right_variation
#print axioms GroundStatePosteriorJoint.fineFrozenProfileEnergy_le_kernelVariationEnergy
#print axioms GroundStatePosteriorJoint.fineFrozenProfileEnergy_le_canonicalKernelVariationEnergy
#print axioms GroundStatePosteriorJoint.fineFrozenKernelInitialVariation_eq_zero
#print axioms GroundStatePosteriorJoint.fineFrozenProfileEnergy_eq_zero_of_kernelRate_zero

end

end MGAP4D.MathlibAnalytic
