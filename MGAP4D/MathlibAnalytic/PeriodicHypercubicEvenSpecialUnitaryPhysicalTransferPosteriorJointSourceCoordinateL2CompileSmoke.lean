import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointSourceCoordinateL2

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

namespace SourceCoordinateL2Smoke

section General
variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "GaugeT" => Matrix.specialUnitaryGroup (Fin N) ℂ
local notation "PairL2" => PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N
local notation "μP" => periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
local notation "μJ" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure H N hN beta hbeta
local notation "Nu" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure H N hN beta hbeta
local notation "J" => jointTransferKernel H N hN beta hbeta
local notation "Obs" => jointTransferBCF H N hN beta hbeta
local notation "Out" => outputRightLinkTilt H N hN beta hbeta
local notation "Resp" => sourceLinkResponse H N hN beta hbeta
local notation "Row" => sourceWeightedRowL2 H N hN beta hbeta
local notation "Proj" => sourceCoordinateProjection H N
local notation "Center" => sourceCenteredCoordinate H N hN beta hbeta
local notation "Tilt" => sourceTiltL2 H N hN beta hbeta
local notation "Avg" => sourceTiltMean H N beta
local notation "Diff" => jointTransferLinkDifference H N hN beta hbeta
local notation "Rate" => (Real.exp (2 * beta) - 1)

theorem sourceSigma (e : Link) :
    sourceCoordinateSigma H N e ≤ (inferInstance : MeasurableSpace Joint) :=
  sourceCoordinateSigma_le H N e

theorem sourceContraction (e : Link) (f : PairL2) : ‖Proj e f‖ ≤ ‖f‖ :=
  sourceCoordinateProjection_norm_le H N e f

theorem signedRowMembership (x : PairL2) (z : Joint) : MemLp (fun y => J y z * x y) 2 μP :=
  sourceWeightedRow_memLp_two H N hN beta hbeta x z

theorem sourceMeasurableTilt (e : Link) (z : Joint) (g : GaugeT) :
    AEStronglyMeasurable[sourceCoordinateSigma H N e] (fun y => Tilt e z g y) μP :=
  sourceTiltL2_source_measurable H N hN beta hbeta e z g

theorem multiplierNorm (e : Link) (z : Joint) (g : GaugeT) : ‖Tilt e z g‖ ≤ Rate :=
  sourceTiltL2_norm_le H N hN beta hbeta e z g

theorem exactSignedProjection (x : PairL2) (e : Link) (z : Joint) (g : GaugeT) :
    Resp x e z g = inner ℝ (Proj e (Row x z)) (Tilt e z g) :=
  sourceLinkResponse_eq_coordinate_inner H N hN beta hbeta x e z g

theorem signedCoordinateBound (x : PairL2) (e : Link) (z : Joint) (g : GaugeT) :
    |Resp x e z g| ≤ Rate * ‖Proj e (Row x z)‖ :=
  sourceLinkResponse_abs_le_coordinateNorm H N hN beta hbeta x e z g

theorem centeredMeanZero (x : PairL2) (e : Link) (z : Joint) :
    (∫ y, Center x e z y ∂μP) = 0 :=
  sourceCenteredCoordinate_integral_zero H N hN beta hbeta x e z

theorem exactCenteredResponse (x : PairL2) (e : Link) (z : Joint) (g : GaugeT) :
    Resp x e z g = Obs x z * Avg e z g + inner ℝ (Center x e z) (Tilt e z g) :=
  sourceLinkResponse_eq_centeredCoordinate H N hN beta hbeta x e z g

theorem originalDefectDrift (x : PairL2) (e : Link) (z : Joint) (g : GaugeT) :
    Diff x e z g = (1 - Out z e g * (1 + Avg e z g)) * Obs x z -
      Out z e g * inner ℝ (Center x e z) (Tilt e z g) :=
  jointTransferLinkDifference_eq_centeredCoordinate H N hN beta hbeta x e z g

theorem originalDefectBound (x : PairL2) (e : Link) (z : Joint) (g : GaugeT) :
    |Diff x e z g| ≤ |1 - Out z e g * (1 + Avg e z g)| * |Obs x z| +
      Out z e g * Rate * ‖Center x e z‖ :=
  jointTransferLinkDifference_abs_le_centeredCoordinate H N hN beta hbeta x e z g

/-- Vanishing centered source response does not justify dropping the output drift. -/
theorem vanishingCoordinateRetainsDrift (x : PairL2) (e : Link) (z : Joint) (g : GaugeT)
    (hc : Center x e z = 0) :
    Diff x e z g = (1 - Out z e g * (1 + Avg e z g)) * Obs x z := by
  rw [jointTransferLinkDifference_eq_centeredCoordinate, hc, inner_zero_left, mul_zero, sub_zero]

theorem zeroCouplingResponse (x : PairL2) (e : Link) (z : Joint) (g : GaugeT) :
    sourceLinkResponse H N hN 0 (by norm_num) x e z g = 0 := by
  have h := sourceLinkResponse_abs_le_coordinateNorm H N hN 0 (by norm_num) x e z g
  have hz : |sourceLinkResponse H N hN 0 (by norm_num) x e z g| ≤ 0 := by
    simpa using h
  exact abs_eq_zero.mp (le_antisymm hz (abs_nonneg _))

theorem originalEnergyHalf (x : PairL2) (e : Link) :
    jointTransferLinkLocalEnergy H N hN beta hbeta x e = (1 / 2 : ℝ) *
      ∫ z, ∫ g, ((1 - Out z e g * (1 + Avg e z g)) * Obs x z -
        Out z e g * inner ℝ (Center x e z) (Tilt e z g)) ^ 2 ∂Nu z.1 z.2 e ∂μJ := by
  have h := jointTransferLinkResamplingEnergy_eq_twice_localEnergy H N hN beta hbeta x e
  rw [jointTransferLinkResamplingEnergy_eq_centeredCoordinate] at h
  linarith

end General

section Frozen
variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ) (k : Fin 3)
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
local notation "Avg" => sourceTiltMean Hn 2 (beta n)
local notation "Center" => sourceCenteredCoordinate Hn 2 Pos (beta n) (hbeta n)
local notation "Tilt" => sourceTiltL2 Hn 2 Pos (beta n) (hbeta n)

theorem sourceCoordinateActualFrozenZeroStep :
    sixColorInitialResidualEnergy Hn 2 Pos (beta n) (hbeta n) Frozen0 =
      (1 / 12 : ℝ) * ∑ e : Link, ∫ z, ∫ g,
        ((1 - Out z e g * (1 + Avg e z g)) * Obs Orbit0 z -
          Out z e g * inner ℝ (Center Orbit0 e z) (Tilt e z g)) ^ 2 ∂Nu z.1 z.2 e ∂μJ :=
  fineFrozenInitialEnergy_eq_centeredCoordinate n 0 k

end Frozen
end SourceCoordinateL2Smoke

#check GroundStatePosteriorJoint.sourceWeightedRow_memLp_two
#check GroundStatePosteriorJoint.sourceLinkResponse_eq_coordinate_inner
#check GroundStatePosteriorJoint.sourceLinkResponse_abs_le_coordinateNorm
#check GroundStatePosteriorJoint.sourceCenteredCoordinate_integral_zero
#check GroundStatePosteriorJoint.sourceLinkResponse_eq_centeredCoordinate
#check GroundStatePosteriorJoint.jointTransferLinkDifference_eq_centeredCoordinate
#check GroundStatePosteriorJoint.jointTransferLinkDifference_abs_le_centeredCoordinate
#check GroundStatePosteriorJoint.fineFrozenInitialEnergy_eq_centeredCoordinate

#print axioms GroundStatePosteriorJoint.sourceCoordinateSigma_le
#print axioms GroundStatePosteriorJoint.sourceCoordinateProjection_norm_le
#print axioms GroundStatePosteriorJoint.sourceWeightedRow_memLp_two
#print axioms GroundStatePosteriorJoint.sourceWeightedRowL2_ae
#print axioms GroundStatePosteriorJoint.sourceTiltValue_source_measurable
#print axioms GroundStatePosteriorJoint.sourceTiltValue_memLp_two
#print axioms GroundStatePosteriorJoint.sourceTiltL2_ae
#print axioms GroundStatePosteriorJoint.sourceTiltL2_source_measurable
#print axioms GroundStatePosteriorJoint.sourceTiltL2_norm_le
#print axioms GroundStatePosteriorJoint.sourceCoordinateProjection_inner
#print axioms GroundStatePosteriorJoint.sourceLinkResponse_eq_row_inner
#print axioms GroundStatePosteriorJoint.sourceLinkResponse_eq_coordinate_inner
#print axioms GroundStatePosteriorJoint.sourceTilt_inner_abs_le
#print axioms GroundStatePosteriorJoint.sourceLinkResponse_abs_le_coordinateNorm
#print axioms GroundStatePosteriorJoint.sourceCenteredCoordinate_norm_le
#print axioms GroundStatePosteriorJoint.sourceCenteredCoordinate_integral_zero
#print axioms GroundStatePosteriorJoint.sourceLinkResponse_eq_centeredCoordinate
#print axioms GroundStatePosteriorJoint.jointTransferLinkDifference_eq_centeredCoordinate
#print axioms GroundStatePosteriorJoint.jointTransferLinkDifference_abs_le_centeredCoordinate
#print axioms GroundStatePosteriorJoint.jointTransferLinkResamplingEnergy_eq_centeredCoordinate
#print axioms GroundStatePosteriorJoint.centeredCoordinateDefect_sq_joint_integrable
#print axioms GroundStatePosteriorJoint.fineFrozenInitialEnergy_eq_centeredCoordinate
#print axioms SourceCoordinateL2Smoke.sourceSigma
#print axioms SourceCoordinateL2Smoke.sourceContraction
#print axioms SourceCoordinateL2Smoke.signedRowMembership
#print axioms SourceCoordinateL2Smoke.sourceMeasurableTilt
#print axioms SourceCoordinateL2Smoke.multiplierNorm
#print axioms SourceCoordinateL2Smoke.exactSignedProjection
#print axioms SourceCoordinateL2Smoke.signedCoordinateBound
#print axioms SourceCoordinateL2Smoke.centeredMeanZero
#print axioms SourceCoordinateL2Smoke.exactCenteredResponse
#print axioms SourceCoordinateL2Smoke.originalDefectDrift
#print axioms SourceCoordinateL2Smoke.originalDefectBound
#print axioms SourceCoordinateL2Smoke.vanishingCoordinateRetainsDrift
#print axioms SourceCoordinateL2Smoke.zeroCouplingResponse
#print axioms SourceCoordinateL2Smoke.originalEnergyHalf
#print axioms SourceCoordinateL2Smoke.sourceCoordinateActualFrozenZeroStep

end
end MGAP4D.MathlibAnalytic
