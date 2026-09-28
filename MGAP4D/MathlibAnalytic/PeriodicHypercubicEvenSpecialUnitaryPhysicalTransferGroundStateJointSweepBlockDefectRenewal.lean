import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepBlockDefectTerminalGeometry
import Mathlib.Tactic

/-!
# Exact renewal identity for the positive-beta sweep--block defect

For one fixed spatial color let

* `B` be the genuine color-block orthogonal projection;
* `S` be the complete canonical same-color one-link sweep;
* `L(x)` be the exact one-pass sweep path loss;
* `D(x) = ||S x - B x||^2` be the sweep--block defect energy.

PR #4880 gives

  ||x - B x||^2 = L(x) + D(x),

while PR #4891 identifies

  D(x) = ||S x - B(S x)||^2.

Applying the first identity to `S x` therefore gives the exact renewal law

  D(x) = L(S x) + D(S x).

Thus one more sweep removes exactly the next-sweep path loss from the current
defect energy.  No convergence theorem, commutativity assumption, response
estimate, or comparison coefficient is used here.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped BigOperators InnerProductSpace InnerProduct

noncomputable section

local instance sweepBlockDefectRenewalSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance sweepBlockDefectRenewalSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Fixed-color recursive residual form:
the color residual before a sweep is the one-pass path loss plus the color
residual of the terminal sweep vector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColor_residual_norm_sq_eq_sweepPathLoss_add_terminalColorResidual_norm_sq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    ‖f -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
          H N hN beta hbeta color f‖ ^ 2 =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss
          H N hN beta hbeta color f +
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
              H N hN beta hbeta color f -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
            H N hN beta hbeta color
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
              H N hN beta hbeta color f)‖ ^ 2 := by
  have h :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColor_residual_norm_sq_eq_sweepPathLoss_add_sweepBlockDefect_norm_sq
      H N hN beta hbeta color f
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefect_norm_sq_eq_terminalColorResidual_norm_sq
      H N hN beta hbeta color f] at h
  exact h

/-- Exact one-step renewal identity for the sweep--block defect:
the current defect equals the path loss of a second sweep plus the defect left
after that second sweep. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefect_norm_sq_eq_terminalSweepPathLoss_add_nextDefect_norm_sq
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
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss
          H N hN beta hbeta color
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
            H N hN beta hbeta color f) +
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
          H N hN beta hbeta color
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
            H N hN beta hbeta color f)‖ ^ 2 := by
  let S :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
      H N hN beta hbeta color f
  have hterminal :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColor_residual_norm_sq_eq_sweepPathLoss_add_terminalColorResidual_norm_sq
      H N hN beta hbeta color S
  calc
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
        H N hN beta hbeta color f‖ ^ 2 =
      ‖S -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
          H N hN beta hbeta color S‖ ^ 2 := by
            simpa [S] using
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefect_norm_sq_eq_terminalColorResidual_norm_sq
                H N hN beta hbeta color f
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss
          H N hN beta hbeta color S +
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
              H N hN beta hbeta color S -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
            H N hN beta hbeta color
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
              H N hN beta hbeta color S)‖ ^ 2 :=
      hterminal
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss
          H N hN beta hbeta color S +
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
          H N hN beta hbeta color S‖ ^ 2 := by
            rw [
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefect_norm_sq_eq_terminalColorResidual_norm_sq
                H N hN beta hbeta color S]

/-- The fixed-color one-link sweep path loss is nonnegative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss
        H N hN beta hbeta color f := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss
  exact
    realHilbertProjectionSweepPathLoss_nonneg
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
        H N hN beta hbeta color)
      ((Finset.univ :
        Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList)
      f

/-- Repeating the same complete color sweep cannot increase the sweep--block
defect energy. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColor_nextSweepBlockDefect_norm_sq_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
        H N hN beta hbeta color
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
          H N hN beta hbeta color f)‖ ^ 2 ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
        H N hN beta hbeta color f‖ ^ 2 := by
  have hRenew :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefect_norm_sq_eq_terminalSweepPathLoss_add_nextDefect_norm_sq
      H N hN beta hbeta color f
  have hLoss :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss_nonneg
      H N hN beta hbeta color
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
        H N hN beta hbeta color f)
  linarith

/-- Abstract contraction receiver.
If one additional complete color sweep leaves at most a fraction `rho` of the
current defect, then the terminal-sweep path loss controls `(1-rho)` times
the current defect energy. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColor_terminalSweepPathLoss_ge_one_sub_rho_mul_defect
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (rho : ℝ)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hnext :
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
          H N hN beta hbeta color
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
            H N hN beta hbeta color f)‖ ^ 2 ≤
        rho *
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
            H N hN beta hbeta color f‖ ^ 2) :
    (1 - rho) *
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
          H N hN beta hbeta color f‖ ^ 2 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss
        H N hN beta hbeta color
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
          H N hN beta hbeta color f) := by
  have hRenew :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefect_norm_sq_eq_terminalSweepPathLoss_add_nextDefect_norm_sq
      H N hN beta hbeta color f
  linarith

/-- Two-input receiver.
Combining a contraction of the next defect with a bound of the terminal-sweep
path loss by `eta` times the original path loss yields the coefficient-preserving
inequality

  (1-rho) * defect <= eta * originalPathLoss.

This avoids division until a later theorem has a certified positive
`1-rho`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColor_one_sub_rho_mul_defect_le_eta_mul_sweepPathLoss
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (rho eta : ℝ)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hnext :
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
          H N hN beta hbeta color
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
            H N hN beta hbeta color f)‖ ^ 2 ≤
        rho *
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
            H N hN beta hbeta color f‖ ^ 2)
    (hterminal :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss
          H N hN beta hbeta color
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
            H N hN beta hbeta color f) ≤
        eta *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss
            H N hN beta hbeta color f) :
    (1 - rho) *
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
          H N hN beta hbeta color f‖ ^ 2 ≤
      eta *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss
          H N hN beta hbeta color f := by
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColor_terminalSweepPathLoss_ge_one_sub_rho_mul_defect
      H N hN beta hbeta color rho f hnext).trans hterminal

end

end MGAP4D.MathlibAnalytic
