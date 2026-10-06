import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentExactBCF

/-! Compile contracts for literal transfer smoothing and the actual frozen family. -/
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

local instance exactBCFSmokePairProbability (H N : ℕ) :
    IsProbabilityMeasure (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

#check GroundStatePosteriorJoint.pairTransferIntegral_continuous
#check GroundStatePosteriorJoint.pairTransferBCF_rep_eq
#check GroundStatePosteriorJoint.continuousJointSqrtDensity_ae_eq
#check GroundStatePosteriorJoint.jointTransferBCF_rep_eq
#check GroundStatePosteriorJoint.fineFrozenBCF_rep_eq
#check GroundStatePosteriorJoint.fineFrozenBCF_approximation_error
#check GroundStatePosteriorJoint.fineFrozenBCF_leftCentered_error
#check GroundStatePosteriorJoint.fineFrozenLeftQuotientMajorant_eq_energy
#check GroundStatePosteriorJoint.fineFrozenProfileEnergy_le_constructedAnchorEnergy
#check GroundStatePosteriorJoint.fineFrozenProfileEnergy_le_canonicalAnchorEnergy

section General
variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "μP" => periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
local notation "PairL2" => PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N
local notation "NormTransfer" => periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator H N hN beta hbeta
local notation "BCFRep" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF H N hN beta hbeta
local notation "UJoint" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv H N hN beta hbeta

example (f : PairL2) : Continuous (pairTransferIntegral H N beta f) :=
  pairTransferIntegral_continuous H N hN beta hbeta f

example (f : PairL2) (z : Joint) : Integrable (fun x =>
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel H N beta (x, z) * f x) μP :=
  pairTransferIntegrand_integrable H N hN beta hbeta f z

example (f : PairL2) : BoundedContinuousFunction.toLp 2 μP ℝ
    (pairTransferBCF H N hN beta hbeta f) = NormTransfer f :=
  pairTransferBCF_rep_eq H N hN beta hbeta f

example (z : Joint) : 0 < continuousJointSqrtDensity H N hN beta hbeta z :=
  continuousJointSqrtDensity_pos H N hN beta hbeta z

example (z : Joint) : continuousJointSqrtDensity H N hN beta hbeta z ^ 2 =
    continuousJointWeight H N hN beta hbeta z :=
  Real.sq_sqrt (continuousJointWeight_pos H N hN beta hbeta z).le

example (f : PairL2) : BCFRep (jointTransferBCF H N hN beta hbeta f) = UJoint (NormTransfer f) :=
  jointTransferBCF_rep_eq H N hN beta hbeta f

example (f : PairL2) : ‖BCFRep (jointTransferBCF H N hN beta hbeta f)‖ = ‖NormTransfer f‖ :=
  jointTransferBCF_rep_norm H N hN beta hbeta f
end General

section FrozenExamples
variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ) (k : Fin 3)
local notation "Hn" => halfExtent (n + 1)
local notation "Pos" => specialUnitaryTwoWilsonRankPositive
local notation "BCFRep" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF Hn 2 Pos (beta n) (hbeta n)
local notation "Frozen" => physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k
local notation "O" => fineFrozenBCF (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k
local notation "Center" => posteriorLeftCenteredOperator Hn 2 Pos (beta n) (hbeta n)
local notation "ResponseData" => PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteExpectationResponseMatrixData Hn 2 Pos (beta n) (hbeta n)
local notation "OscEnergy" => periodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageOscillationEnergy Hn
local notation "V" => fineFrozenAnchoredInitialVariation (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k

example : BCFRep O = Frozen := fineFrozenBCF_rep_eq n r k

example : ‖Frozen - BCFRep O‖ = 0 := fineFrozenBCF_approximation_error n r k

example : ‖Center (Frozen - BCFRep O)‖ = 0 := fineFrozenBCF_leftCentered_error n r k

example : BCFRep (fineFrozenBCF (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 0 k) =
    physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 0 k :=
  fineFrozenBCF_rep_eq n 0 k

example (R : ResponseData) :
    leftQuotientMajorant Hn 2 Pos (beta n) (hbeta n) R O V Frozen =
      OscEnergy (posteriorSixColorVariationProfile Hn 2 Pos (beta n) (hbeta n) R V) :=
  fineFrozenLeftQuotientMajorant_eq_energy n r k R V

example (R : ResponseData) :
    physicalYangMillsSU2AdjacentFineGroundStateSweepStageProfileEnergy
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k ≤
      OscEnergy (posteriorSixColorVariationProfile Hn 2 Pos (beta n) (hbeta n) R V) :=
  fineFrozenProfileEnergy_le_constructedAnchorEnergy n r k R
end FrozenExamples

#print axioms GroundStatePosteriorJoint.pairTransferIntegrand_integrable
#print axioms GroundStatePosteriorJoint.pairTransferIntegral_continuous
#print axioms GroundStatePosteriorJoint.pairTransferIntegral_norm_le_integral_norm
#print axioms GroundStatePosteriorJoint.pairTransferIntegral_ae_eq
#print axioms GroundStatePosteriorJoint.pairTransferBCF_rep_eq
#print axioms GroundStatePosteriorJoint.continuousJointWeight_continuous
#print axioms GroundStatePosteriorJoint.continuousJointWeight_pos
#print axioms GroundStatePosteriorJoint.continuousJointWeight_ae_eq
#print axioms GroundStatePosteriorJoint.continuousJointSqrtDensity_ae_eq
#print axioms GroundStatePosteriorJoint.jointTransferBCF_rep_eq
#print axioms GroundStatePosteriorJoint.jointTransferBCF_rep_norm
#print axioms GroundStatePosteriorJoint.fineFrozenBCF_rep_eq
#print axioms GroundStatePosteriorJoint.fineFrozenBCF_approximation_error
#print axioms GroundStatePosteriorJoint.fineFrozenBCF_leftCentered_error
#print axioms GroundStatePosteriorJoint.fineFrozenLeftQuotientMajorant_eq_energy
#print axioms GroundStatePosteriorJoint.fineFrozenProfileEnergy_le_constructedAnchorEnergy
#print axioms GroundStatePosteriorJoint.fineFrozenProfileEnergy_le_canonicalAnchorEnergy

end

end MGAP4D.MathlibAnalytic
