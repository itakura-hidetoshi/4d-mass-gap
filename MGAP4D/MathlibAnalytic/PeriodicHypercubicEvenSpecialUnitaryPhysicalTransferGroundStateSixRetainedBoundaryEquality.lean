import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointSixRetainedLpMeasReverse
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointTwoSidedTwelveSpatialConditionalExpectation
import Mathlib.Tactic

/-!
# Exact six-retained boundary subspaces

The existing finite-product/Fubini argument proves that the intersection of all
six right-retained ground-state spatial-color L² subspaces is contained in the
complete left-boundary L² subspace.  The reverse inclusion is immediate from
the fact that every right spatial-color sigma-algebra retains the whole left
boundary.

This file closes that equality, together with its left/right symmetric version.
The statement is qualitative and valid for every nonnegative beta; it introduces
no commutation or quantitative Poincare claim.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The complete left-boundary measurable subspace is contained in every
right-color retained subspace simultaneously. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundState_fst_lpMeas_le_rightSixRetained
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    lpMeas ℝ ℝ
        (MeasurableSpace.comap Prod.fst
          (inferInstance : MeasurableSpace
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)))
        2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightSixRetainedLpMeas
        H N hN beta hbeta := by
  intro z hz
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightSixRetainedLpMeas,
    Submodule.mem_iInf]
  intro c
  apply mem_lpMeas_iff_aestronglyMeasurable.mpr
  exact
    (mem_lpMeas_iff_aestronglyMeasurable.mp hz).mono
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftMeasurableSpace_le_spatialColor
        H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c))

/-- Exact identification of the common range of all six right-color retained
subspaces with the complete left-boundary measurable L² subspace. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightSixRetainedLpMeas_eq_fst
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightSixRetainedLpMeas
        H N hN beta hbeta =
      lpMeas ℝ ℝ
        (MeasurableSpace.comap Prod.fst
          (inferInstance : MeasurableSpace
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)))
        2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta) := by
  apply le_antisymm
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightSixRetainedLpMeas_le_fst
        H N hN beta hbeta
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundState_fst_lpMeas_le_rightSixRetained
        H N hN beta hbeta

/-- The complete right-boundary measurable subspace is contained in every
left-color retained subspace simultaneously. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundState_snd_lpMeas_le_leftSixRetained
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    lpMeas ℝ ℝ
        (MeasurableSpace.comap Prod.snd
          (inferInstance : MeasurableSpace
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)))
        2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixRetainedLpMeas
        H N hN beta hbeta := by
  intro z hz
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixRetainedLpMeas,
    Submodule.mem_iInf]
  intro c
  apply mem_lpMeas_iff_aestronglyMeasurable.mpr
  exact
    (mem_lpMeas_iff_aestronglyMeasurable.mp hz).mono
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointRightMeasurableSpace_le_leftSpatialColor
        H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c))

/-- Left/right symmetric exact identification: all six left-color retained
subspaces intersect in the complete right-boundary measurable L² subspace. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixRetainedLpMeas_eq_snd
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixRetainedLpMeas
        H N hN beta hbeta =
      lpMeas ℝ ℝ
        (MeasurableSpace.comap Prod.snd
          (inferInstance : MeasurableSpace
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)))
        2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta) := by
  apply le_antisymm
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixRetainedLpMeas_le_snd
        H N hN beta hbeta
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundState_snd_lpMeas_le_leftSixRetained
        H N hN beta hbeta

end

end MGAP4D.MathlibAnalytic
