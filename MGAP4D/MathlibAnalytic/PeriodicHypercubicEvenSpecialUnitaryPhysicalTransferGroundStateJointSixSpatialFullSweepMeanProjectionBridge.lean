import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepBlockDefectPythagoras
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateSixSpatialMeanProjectionGap
import Mathlib.Tactic

/-!
# Full one-link sweep mean versus genuine six-spatial mean projection

PR #4880 identifies the exact positive-beta obstruction between the genuine
six-spatial block residual and the canonical one-link sweep path loss.

This file records the equivalent retained-norm identity

  mean_c ||S_c f||^2
    =
  mean_c ||B_c f||^2
    + mean_c ||S_c f - B_c f||^2,

where `S_c` is the complete canonical same-color one-link sweep and `B_c`
is the genuine spatial-color conditional expectation.

Hence the genuine mean projected norm is bounded by the full-sweep mean norm
with coefficient one.  Any strict volume-uniform contraction of the full
one-link sweep therefore immediately implies the already-established
six-spatial mean-projection contraction and physical transfer gap.

No target/source cardinality factor, Cauchy loss, factor two, commutativity
assumption, or new comparison coefficient is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped BigOperators InnerProductSpace InnerProduct

noncomputable section

local instance sixSpatialFullSweepMeanProjectionBridgeSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The six-color mean sweep--block defect energy is nonnegative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepBlockDefectMeanNormSq_nonneg
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepBlockDefectMeanNormSq
        H N hN beta hbeta f := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepBlockDefectMeanNormSq
  positivity

/-- Exact retained-norm form of PR #4880:
the terminal full-sweep mean norm equals the genuine six-color mean projected
norm plus the sweep--block defect mean energy. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkFullSweepMeanNormSq_eq_meanProjectedNormSq_add_sweepBlockDefectMeanNormSq
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkFullSweepMeanNormSq
        H N hN beta hbeta f =
      groundStateJointColorMeanProjectedNormSq
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2
            H N hN beta hbeta) f +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepBlockDefectMeanNormSq
          H N hN beta hbeta f := by
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2
      H N hN beta hbeta
  let S :=
    fun c : Fin 6 =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
        H N hN beta hbeta
        (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f
  let D :=
    fun c : Fin 6 =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
        H N hN beta hbeta
        (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f
  have hEach :
      ∀ c : Fin 6,
        ‖S c‖ ^ 2 = ‖P c f‖ ^ 2 + ‖D c‖ ^ 2 := by
    intro c
    let color :=
      periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c
    have hResidual :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColor_residual_norm_sq_eq_sweepPathLoss_add_sweepBlockDefect_norm_sq
        H N hN beta hbeta color f
    have hPath :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss_eq_norm_sq_sub_fullSweep_norm_sq
        H N hN beta hbeta color f
    have hBlock :=
      realHilbertProjection_residual_norm_sq
        (P c)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2_idempotent
          H N hN beta hbeta c)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2_symmetric
          H N hN beta hbeta c)
        f
    have hResidual' :
        ‖f - P c f‖ ^ 2 =
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss
              H N hN beta hbeta color f +
            ‖D c‖ ^ 2 := by
      simpa [P, D, color] using hResidual
    have hPath' :
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss
            H N hN beta hbeta color f =
          ‖f‖ ^ 2 - ‖S c‖ ^ 2 := by
      simpa [S, color] using hPath
    have hBlock' :
        ‖f - P c f‖ ^ 2 = ‖f‖ ^ 2 - ‖P c f‖ ^ 2 := by
      simpa using hBlock
    rw [hBlock', hPath'] at hResidual'
    nlinarith
  have hSum :
      (∑ c : Fin 6, ‖S c‖ ^ 2) =
        (∑ c : Fin 6, ‖P c f‖ ^ 2) +
          ∑ c : Fin 6, ‖D c‖ ^ 2 := by
    calc
      (∑ c : Fin 6, ‖S c‖ ^ 2) =
          ∑ c : Fin 6, (‖P c f‖ ^ 2 + ‖D c‖ ^ 2) := by
            apply Finset.sum_congr rfl
            intro c _hc
            exact hEach c
      _ = _ := by
        rw [Finset.sum_add_distrib]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkFullSweepMeanNormSq
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepBlockDefectMeanNormSq
    groundStateJointColorMeanProjectedNormSq
  change
    (1 / 6 : ℝ) * ∑ c : Fin 6, ‖S c‖ ^ 2 =
      ((Fintype.card (Fin 6) : ℝ)⁻¹) * ∑ c : Fin 6, ‖P c f‖ ^ 2 +
        (1 / 6 : ℝ) * ∑ c : Fin 6, ‖D c‖ ^ 2
  rw [hSum]
  norm_num
  ring

/-- The genuine six-spatial mean projected norm is bounded by the complete
one-link full-sweep mean norm, with coefficient one. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatial_meanProjectedNormSq_le_fullSweepMeanNormSq
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    groundStateJointColorMeanProjectedNormSq
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2
          H N hN beta hbeta) f ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkFullSweepMeanNormSq
        H N hN beta hbeta f := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkFullSweepMeanNormSq_eq_meanProjectedNormSq_add_sweepBlockDefectMeanNormSq]
  exact
    le_add_of_nonneg_right
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepBlockDefectMeanNormSq_nonneg
        H N hN beta hbeta f)

section FiniteVolume

variable (H N : ℕ)
variable (hN : 0 < N)
variable (beta : ℝ)
variable (hbeta : 0 ≤ beta)

local notation "HaarL2" =>
  Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
local notation "G" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
    H N hN beta hbeta
local notation "V" =>
  PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateVacuumL2
    H N hN beta hbeta
local notation "U" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
    H N hN beta hbeta
local notation "R" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift
    H N hN beta hbeta

/-- A contraction of the complete same-color one-link sweeps on the physical
top-orthogonal sector implies the existing six-spatial mean-projection
contraction, hence the explicit physical transfer-gap lower bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkFullSweepMeanContraction_implies_transferGap
    (q : ℝ)
    (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1)
    (hcontract : ∀ x : K,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkFullSweepMeanNormSq
          H N hN beta hbeta (R (U ((x : G) : HaarL2))) ≤
        q * ‖(x : G)‖ ^ 2) :
    3 * (1 - q) / 8 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
        H N hN beta hbeta := by
  apply
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialMeanProjectionContraction_implies_transferGap
      H N hN beta hbeta q hq0 hq1
  intro x
  have hMean :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialMeanProjectedNormSq
          H N hN beta hbeta (U ((x : G) : HaarL2)) ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkFullSweepMeanNormSq
          H N hN beta hbeta (R (U ((x : G) : HaarL2))) := by
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialMeanProjectedNormSq] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatial_meanProjectedNormSq_le_fullSweepMeanNormSq
        H N hN beta hbeta (R (U ((x : G) : HaarL2)))
  exact hMean.trans (hcontract x)

/-- Strict contraction of the complete same-color one-link sweeps yields a
strictly positive finite-volume physical transfer gap. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkFullSweepMeanContraction_positive_transferGap
    (q : ℝ)
    (hq0 : 0 ≤ q)
    (hq1 : q < 1)
    (hcontract : ∀ x : K,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkFullSweepMeanNormSq
          H N hN beta hbeta (R (U ((x : G) : HaarL2))) ≤
        q * ‖(x : G)‖ ^ 2) :
    0 <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
        H N hN beta hbeta := by
  have hgap :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkFullSweepMeanContraction_implies_transferGap
      H N hN beta hbeta q hq0 hq1.le hcontract
  have hpos : 0 < 3 * (1 - q) / 8 := by
    positivity
  exact lt_of_lt_of_le hpos hgap

end FiniteVolume

end

end MGAP4D.MathlibAnalytic
