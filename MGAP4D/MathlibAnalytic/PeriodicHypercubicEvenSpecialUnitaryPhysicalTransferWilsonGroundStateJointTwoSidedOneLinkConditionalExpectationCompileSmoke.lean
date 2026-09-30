import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointTwoSidedOneLinkConditionalExpectation

open MGAP4D.MathlibAnalytic
open MeasureTheory

noncomputable section

#check periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialLinkMeasurableSpace
#check periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialLinkMeasurableSpace_le
#check periodicHypercubicEvenSpecialUnitaryGroundStateJointRightMeasurableSpace_le_leftSpatialLink
#check periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace_le_leftSpatialLink
#check periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
#check periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2_apply
#check periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2_idempotent
#check periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2_symmetric
#check periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2_residual_norm_le_color
#check periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2_residual_sq_le_color
#check PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink
#check periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2

-- The Sum orientation agrees with the existing twelve-color convention:
-- inl updates the right boundary and inr updates the left boundary.
example (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
        H N hN beta hbeta (Sum.inl target) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
        H N hN beta hbeta target := rfl

example (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
        H N hN beta hbeta (Sum.inr target) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
        H N hN beta hbeta target := rfl

#print axioms periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace_le_leftSpatialLink
#print axioms periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2_idempotent
#print axioms periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2_symmetric
#print axioms periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2_residual_sq_le_color

end
