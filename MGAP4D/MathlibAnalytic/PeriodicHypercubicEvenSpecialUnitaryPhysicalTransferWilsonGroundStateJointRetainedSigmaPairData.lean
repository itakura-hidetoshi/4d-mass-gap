import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointSpatialCoordinateMeasurableEquiv
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointTwoSidedTwelveSpatialConditionalExpectation
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance groundStateJointRetainedSigmaPairDataMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- The data literally retained by a right-boundary color update, packaged as
one map: the complete left boundary together with the off-color part of the
right boundary. -/
def periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedPairData
    (H N : ℕ)
    (c : Fin 6) :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) →
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (PeriodicHypercubicEvenSpatialSliceOffColorLink H
            (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) →
          Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
  fun z =>
    (z.1,
      periodicHypercubicEvenSpatialSliceOffColorRestriction
        (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) z.2)

/-- The right retained pair-data map is measurable. -/
theorem
    measurable_periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedPairData
    (H N : ℕ)
    (c : Fin 6) :
    Measurable
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedPairData H N c) := by
  exact measurable_fst.prodMk
    ((measurable_periodicHypercubicEvenSpecialUnitarySpatialSliceOffColorRestriction
      H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)).comp measurable_snd)

/-- The pre-existing right-color retained sigma-algebra is exactly the pullback
of the single retained pair-data map.  This merely normalizes the two-channel
supremum presentation via `MeasurableSpace.comap_prodMk`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace_eq_comap_rightRetainedPairData
    (H N : ℕ)
    (c : Fin 6) :
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
        H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) =
      MeasurableSpace.comap
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedPairData H N c)
        inferInstance := by
  unfold periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
  unfold periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedPairData
  symm
  exact MeasurableSpace.comap_prodMk _ _

/-- The data literally retained by a left-boundary color update, packaged as
one map: the complete right boundary together with the off-color part of the
left boundary. -/
def periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedPairData
    (H N : ℕ)
    (c : Fin 6) :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) →
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (PeriodicHypercubicEvenSpatialSliceOffColorLink H
            (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) →
          Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
  fun z =>
    (z.2,
      periodicHypercubicEvenSpatialSliceOffColorRestriction
        (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) z.1)

/-- The left retained pair-data map is measurable. -/
theorem
    measurable_periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedPairData
    (H N : ℕ)
    (c : Fin 6) :
    Measurable
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedPairData H N c) := by
  exact measurable_snd.prodMk
    ((measurable_periodicHypercubicEvenSpecialUnitarySpatialSliceOffColorRestriction
      H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)).comp measurable_fst)

/-- The pre-existing left-color retained sigma-algebra is exactly the pullback
of the single retained pair-data map. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace_eq_comap_leftRetainedPairData
    (H N : ℕ)
    (c : Fin 6) :
    periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
        H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) =
      MeasurableSpace.comap
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedPairData H N c)
        inferInstance := by
  unfold periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
  unfold periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedPairData
  symm
  exact MeasurableSpace.comap_prodMk _ _

end

end MathlibAnalytic
end MGAP4D
