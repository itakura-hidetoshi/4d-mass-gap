import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialOneLinkSweepContractionReceiver
import Mathlib.Tactic

/-!
# Exact sweep--block defect Pythagoras

For one spatial color let

* `B_c` be the genuine spatial-color conditional expectation;
* `S_c` be the complete canonical ordered sweep of all one-link conditional
  expectations in that color.

The retained sigma algebra of `B_c` is contained in the retained sigma
algebra of every one-link projection of color `c`.  Hence `B_c` absorbs
every step and therefore the complete sweep:

  B_c (S_c f) = B_c f.

Since `B_c` is an orthogonal projection, exact Pythagoras at `S_c f` gives

  ||S_c f||^2
    = ||B_c f||^2 + ||S_c f - B_c f||^2.

Combining this with the exact sweep norm loss yields

  ||f - B_c f||^2
    = pathLoss_c(f) + ||S_c f - B_c f||^2.

Averaging over the six spatial colors gives the exact obstruction identity

  sixSpatialResidualEnergy(f)
    =
  sixSpatialOneLinkSweepPathLoss(f)
    + mean_c ||S_c f - B_c f||^2.

Thus the positive-beta gap between the genuine six-color residual and the
ordered one-link path loss is not a target-cardinality term: it is exactly the
six-color mean sweep--block defect energy.
-/

namespace MGAP4D.MathlibAnalytic

open scoped BigOperators InnerProductSpace InnerProduct

noncomputable section

local instance sixSpatialSweepBlockDefectPythagorasSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The complete same-color one-link sweep is absorbed by the coarser
spatial-color conditional expectation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2_fullOneLinkSweep_eq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
        H N hN beta hbeta color
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
          H N hN beta hbeta color f) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
        H N hN beta hbeta color f := by
  let B :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
      H N hN beta hbeta color
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
      H N hN beta hbeta color
  let cs :=
    ((Finset.univ :
      Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList)
  have hAbsorb :
      ∀ e ∈ cs, ∀ x, B (P e x) = B x := by
    intro e _he x
    have hComp :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2_comp_spatialLinkCondExpL2_eq_color
        H N hN beta hbeta color e.1 e.2
    have hApply := congrArg
      (fun T :
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
            H N hN beta hbeta →L[ℝ]
          PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
            H N hN beta hbeta =>
        T x) hComp
    simpa [
      B, P,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2] using
      hApply
  have h :=
    realHilbertNestedBlock_projectionSweep_absorb B P cs hAbsorb f
  simpa [
    B, P, cs,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector] using
    h

/-- Difference between the terminal same-color one-link sweep and the genuine
spatial-color block projection. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
      H N hN beta hbeta color f -
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
      H N hN beta hbeta color f

/-- Exact fixed-color Pythagorean split of the genuine color residual into
ordered one-link sweep path loss plus the sweep--block defect energy. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColor_residual_norm_sq_eq_sweepPathLoss_add_sweepBlockDefect_norm_sq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    ‖f -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
          H N hN beta hbeta color f‖ ^ 2 =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss
          H N hN beta hbeta color f +
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
          H N hN beta hbeta color f‖ ^ 2 := by
  let B :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
      H N hN beta hbeta color
  let S :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
      H N hN beta hbeta color f
  have hBlock :=
    realHilbertProjection_residual_norm_sq
      B
      (by
        simpa [B] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2_idempotent
            H N hN beta hbeta color)
      (by
        intro x y
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2_symmetric
            H N hN beta hbeta color x y)
      f
  have hAbsorb :
      B S = B f := by
    simpa [B, S] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2_fullOneLinkSweep_eq
        H N hN beta hbeta color f
  have hSweepBlock :=
    realHilbertProjection_residual_norm_sq
      B
      (by
        simpa [B] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2_idempotent
            H N hN beta hbeta color)
      (by
        intro x y
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2_symmetric
            H N hN beta hbeta color x y)
      S
  rw [hAbsorb] at hSweepBlock
  have hPath :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss_eq_norm_sq_sub_fullSweep_norm_sq
      H N hN beta hbeta color f
  change
    ‖f - B f‖ ^ 2 =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss
          H N hN beta hbeta color f +
        ‖S - B f‖ ^ 2
  rw [hBlock, hPath]
  change
    ‖f‖ ^ 2 - ‖B f‖ ^ 2 =
      (‖f‖ ^ 2 - ‖S‖ ^ 2) + ‖S - B f‖ ^ 2
  rw [hSweepBlock]
  ring

/-- Six-color mean squared sweep--block defect energy. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepBlockDefectMeanNormSq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) : ℝ :=
  (1 / 6 : ℝ) *
    ∑ c : Fin 6,
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
        H N hN beta hbeta
        (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f‖ ^ 2

/-- Exact global obstruction identity: the genuine six-spatial block residual
is the ordered one-link path loss plus the six-color mean sweep--block defect
energy. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSixSpatialResidualEnergy_eq_sweepPathLoss_add_sweepBlockDefectMeanNormSq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSixSpatialResidualEnergy
        H N hN beta hbeta f =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepPathLoss
          H N hN beta hbeta f +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepBlockDefectMeanNormSq
          H N hN beta hbeta f := by
  have hEach :
      ∀ c : Fin 6,
        ‖f -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
              H N hN beta hbeta
              (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f‖ ^ 2 =
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss
              H N hN beta hbeta
              (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f +
            ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
              H N hN beta hbeta
              (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f‖ ^ 2 := by
    intro c
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColor_residual_norm_sq_eq_sweepPathLoss_add_sweepBlockDefect_norm_sq
        H N hN beta hbeta
        (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f
  have hSum :
      (∑ c : Fin 6,
        ‖f -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
              H N hN beta hbeta
              (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f‖ ^ 2) =
        (∑ c : Fin 6,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss
            H N hN beta hbeta
            (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f) +
        ∑ c : Fin 6,
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
            H N hN beta hbeta
            (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f‖ ^ 2 := by
    calc
      (∑ c : Fin 6,
        ‖f -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
              H N hN beta hbeta
              (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f‖ ^ 2) =
          ∑ c : Fin 6,
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss
                H N hN beta hbeta
                (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f +
              ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
                H N hN beta hbeta
                (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f‖ ^ 2) := by
            apply Finset.sum_congr rfl
            intro c _hc
            exact hEach c
      _ = _ := by
        rw [Finset.sum_add_distrib]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSixSpatialResidualEnergy
    groundStateJointColorNormalizedResidualEnergy
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepPathLoss
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepBlockDefectMeanNormSq
  simp only [Fintype.card_fin]
  rw [hSum]
  norm_num
  ring

/-- Equivalent difference form of the exact obstruction identity. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSixSpatialResidualEnergy_sub_sweepPathLoss_eq_sweepBlockDefectMeanNormSq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSixSpatialResidualEnergy
        H N hN beta hbeta f -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepPathLoss
        H N hN beta hbeta f =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepBlockDefectMeanNormSq
        H N hN beta hbeta f := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSixSpatialResidualEnergy_eq_sweepPathLoss_add_sweepBlockDefectMeanNormSq]
  ring

end

end MGAP4D.MathlibAnalytic
