import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointFixedColorCommonFixedGeometry
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialFullSweepMeanProjectionBridge
import Mathlib.Tactic

/-!
# Terminal geometry of the positive-beta sweep--block defect

For one spatial color write

* `S_c f` for the terminal vector after the complete canonical one-link sweep;
* `B_c f` for the genuine spatial-color conditional expectation.

PR #4880 proves the exact absorption law

  B_c (S_c f) = B_c f,

and PR #4890 proves that `S_c` and `B_c` have exactly the same fixed vectors
for every nonnegative coupling.

Therefore the sweep--block defect is literally the residual of the terminal
sweep vector from the common fixed space:

  S_c f - B_c f = S_c f - B_c (S_c f).

In particular the defect vanishes exactly when one sweep has already landed in
the common fixed space, equivalently when applying the same complete sweep a
second time fixes the terminal vector.

This unit is exact Hilbert geometry.  It introduces no positive-beta
commutativity assumption and no comparison coefficient.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped BigOperators InnerProductSpace InnerProduct

noncomputable section

local instance sweepBlockDefectTerminalGeometrySpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance sweepBlockDefectTerminalGeometrySpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The sweep--block defect is exactly the color-block residual of the terminal
same-color sweep vector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector_eq_terminalColorResidual
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
        H N hN beta hbeta color f =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
          H N hN beta hbeta color f -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
          H N hN beta hbeta color
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
            H N hN beta hbeta color f) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2_fullOneLinkSweep_eq
      H N hN beta hbeta color f]

/-- The sweep--block defect lies in the kernel of the genuine color-block
orthogonal projection. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2_sweepBlockDefectVector_eq_zero
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
        H N hN beta hbeta color
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
          H N hN beta hbeta color f) = 0 := by
  let B :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
      H N hN beta hbeta color
  let S :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
      H N hN beta hbeta color f
  have hAbsorb : B S = B f := by
    simpa [B, S] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2_fullOneLinkSweep_eq
        H N hN beta hbeta color f
  have hIdem :
      B (B f) = B f := by
    have h :=
      congrArg
        (fun T :
          PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
              H N hN beta hbeta →L[ℝ]
            PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
              H N hN beta hbeta =>
          T f)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2_idempotent
          H N hN beta hbeta color)
    simpa [B] using h
  change B (S - B f) = 0
  rw [map_sub, hAbsorb, hIdem, sub_self]

/-- A fixed-color sweep--block defect vanishes exactly when the terminal sweep
vector is already fixed by the genuine color-block projection. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector_eq_zero_iff_terminal_color_fixed
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
        H N hN beta hbeta color f = 0 ↔
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
          H N hN beta hbeta color
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
            H N hN beta hbeta color f) =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
          H N hN beta hbeta color f := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector_eq_terminalColorResidual]
  constructor
  · intro h
    have hs :
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
              H N hN beta hbeta color f =
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
            H N hN beta hbeta color
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
              H N hN beta hbeta color f) :=
      sub_eq_zero.mp h
    exact hs.symm
  · intro h
    exact sub_eq_zero.mpr h.symm

/-- Equivalently, the sweep--block defect vanishes exactly when the terminal
vector is fixed by a second application of the same complete one-link sweep.
Thus the defect is the exact obstruction to one-pass idempotence. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector_eq_zero_iff_terminal_fullSweep_fixed
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
        H N hN beta hbeta color f = 0 ↔
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
          H N hN beta hbeta color
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
            H N hN beta hbeta color f) =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
          H N hN beta hbeta color f := by
  let S :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
      H N hN beta hbeta color f
  have hColor :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector_eq_zero_iff_terminal_color_fixed
      H N hN beta hbeta color f
  have hFixed :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweep_fixed_iff_color_fixed
      H N hN beta hbeta color S
  constructor
  · intro h
    exact hFixed.mpr (hColor.mp h)
  · intro h
    exact hColor.mpr (hFixed.mp h)

/-- Squared-norm form: the fixed-color sweep--block defect energy is exactly
the squared terminal color residual. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefect_norm_sq_eq_terminalColorResidual_norm_sq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
        H N hN beta hbeta color f‖ ^ 2 =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
          H N hN beta hbeta color f -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
          H N hN beta hbeta color
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
            H N hN beta hbeta color f)‖ ^ 2 := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector_eq_terminalColorResidual]

/-- Aggregate receiver: a six-color sum bound on terminal color residuals
immediately gives the normalized sweep--block defect majorant required by the
full-sweep transfer-gap route. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepBlockDefectMeanNormSq_le_of_terminalColorResidual_sum_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (delta : ℝ)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hterminal :
      (∑ c : Fin 6,
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
              H N hN beta hbeta
              (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
            H N hN beta hbeta
            (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
              H N hN beta hbeta
              (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f)‖ ^ 2) ≤
        6 * delta * ‖f‖ ^ 2) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepBlockDefectMeanNormSq
        H N hN beta hbeta f ≤
      delta * ‖f‖ ^ 2 := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepBlockDefectMeanNormSq
  have hsum :
      (∑ c : Fin 6,
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
          H N hN beta hbeta
          (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f‖ ^ 2) ≤
        6 * delta * ‖f‖ ^ 2 := by
    simpa only [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefect_norm_sq_eq_terminalColorResidual_norm_sq] using
      hterminal
  have hscaled :=
    mul_le_mul_of_nonneg_left hsum (show 0 ≤ (1 / 6 : ℝ) by norm_num)
  calc
    (1 / 6 : ℝ) *
        ∑ c : Fin 6,
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
            H N hN beta hbeta
            (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f‖ ^ 2 ≤
      (1 / 6 : ℝ) * (6 * delta * ‖f‖ ^ 2) := hscaled
    _ = delta * ‖f‖ ^ 2 := by ring

end

end MGAP4D.MathlibAnalytic
