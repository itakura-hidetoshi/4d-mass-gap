import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialFullSweepMeanProjectionBridge
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroGroundStateSixSpatialGenuinePairHaarTransport
import Mathlib.Tactic

/-!
# Beta-zero full-sweep defect margin

The genuine beta-zero six-spatial mean projection already has the exact
physical contraction coefficient `5/6`.

PR #4881 identifies the complete same-color one-link full-sweep mean norm as

  meanProjectedNormSq + sweepBlockDefectMeanNormSq.

Therefore, on the physical top-orthogonal sector,

  FullSweepMean <= (5/6) ||x||^2 + SweepBlockDefectMean.

This file packages the quantitative margin left for the positive-beta
perturbation route.  Any uniform estimate

  SweepBlockDefectMean <= delta ||x||^2

with `delta < 1/6` yields the strict full-sweep contraction

  q = 5/6 + delta < 1

and hence, through PR #4881, the explicit transfer-gap lower bound

  3 * (1/6 - delta) / 8.

No cardinality factor, factor two, response symmetry, or new probabilistic
comparison is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped BigOperators InnerProductSpace InnerProduct

noncomputable section

local instance betaZeroFullSweepDefectMarginSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

section FiniteVolume

variable (H N : ℕ)
variable (hN : 0 < N)

local notation "HaarL2" =>
  Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
local notation "G" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N
local notation "K0" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
    H N hN 0 (by norm_num)
local notation "U0" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
    H N hN 0 (by norm_num)
local notation "R0" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift
    H N hN 0 (by norm_num)

/-- Exact beta-zero upper decomposition: the full one-link sweep mean is
bounded by the known `5/6` physical mean-projection contraction plus the
remaining sweep--block defect energy. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPhysicalSixSpatialFullSweepMean_le_fiveSix_norm_sq_add_sweepBlockDefect
    (x : K0) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkFullSweepMeanNormSq
        H N hN 0 (by norm_num)
        (R0 (U0 ((x : G) : HaarL2))) ≤
      (5 / 6 : ℝ) * ‖(x : G)‖ ^ 2 +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepBlockDefectMeanNormSq
          H N hN 0 (by norm_num)
          (R0 (U0 ((x : G) : HaarL2))) := by
  have hMean :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPhysicalSixSpatialMeanProjection_five_six
      H N hN x
  have hExact :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkFullSweepMeanNormSq_eq_meanProjectedNormSq_add_sweepBlockDefectMeanNormSq
      H N hN 0 (by norm_num)
      (R0 (U0 ((x : G) : HaarL2)))
  rw [hExact]
  have hMean' :
      groundStateJointColorMeanProjectedNormSq
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2
            H N hN 0 (by norm_num))
          (R0 (U0 ((x : G) : HaarL2))) ≤
        (5 / 6 : ℝ) * ‖(x : G)‖ ^ 2 := by
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialMeanProjectedNormSq,
      R0, U0] using hMean
  exact add_le_add_right hMean' _

/-- A beta-zero sweep--block defect majorant by `delta` gives full-sweep
contraction with rate `5/6 + delta`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPhysicalSixSpatialFullSweepMean_le_fiveSix_add_delta_of_sweepBlockDefect
    (delta : ℝ)
    (hDefect :
      ∀ x : K0,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepBlockDefectMeanNormSq
            H N hN 0 (by norm_num)
            (R0 (U0 ((x : G) : HaarL2))) ≤
          delta * ‖(x : G)‖ ^ 2)
    (x : K0) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkFullSweepMeanNormSq
        H N hN 0 (by norm_num)
        (R0 (U0 ((x : G) : HaarL2))) ≤
      ((5 / 6 : ℝ) + delta) * ‖(x : G)‖ ^ 2 := by
  have hBase :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPhysicalSixSpatialFullSweepMean_le_fiveSix_norm_sq_add_sweepBlockDefect
      H N hN x
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkFullSweepMeanNormSq
        H N hN 0 (by norm_num)
        (R0 (U0 ((x : G) : HaarL2))) ≤
      (5 / 6 : ℝ) * ‖(x : G)‖ ^ 2 +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepBlockDefectMeanNormSq
          H N hN 0 (by norm_num)
          (R0 (U0 ((x : G) : HaarL2))) := hBase
    _ ≤
      (5 / 6 : ℝ) * ‖(x : G)‖ ^ 2 +
        delta * ‖(x : G)‖ ^ 2 := by
      exact add_le_add_left (hDefect x) _
    _ = ((5 / 6 : ℝ) + delta) * ‖(x : G)‖ ^ 2 := by
      ring

/-- Quantitative beta-zero defect-margin receiver.

Any uniform sweep--block defect coefficient strictly below `1/6` preserves
strict full-sweep contraction and yields an explicit physical transfer-gap
lower bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPhysicalSixSpatial_sweepBlockDefectMargin_implies_transferGap
    (delta : ℝ)
    (hdelta0 : 0 ≤ delta)
    (hdelta : delta < 1 / 6)
    (hDefect :
      ∀ x : K0,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepBlockDefectMeanNormSq
            H N hN 0 (by norm_num)
            (R0 (U0 ((x : G) : HaarL2))) ≤
          delta * ‖(x : G)‖ ^ 2) :
    3 * ((1 / 6 : ℝ) - delta) / 8 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
        H N hN 0 (by norm_num) := by
  let q : ℝ := (5 / 6 : ℝ) + delta
  have hq0 : 0 ≤ q := by
    dsimp [q]
    linarith
  have hq1 : q ≤ 1 := by
    dsimp [q]
    linarith
  have hContract :
      ∀ x : K0,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkFullSweepMeanNormSq
            H N hN 0 (by norm_num)
            (R0 (U0 ((x : G) : HaarL2))) ≤
          q * ‖(x : G)‖ ^ 2 := by
    intro x
    simpa [q] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPhysicalSixSpatialFullSweepMean_le_fiveSix_add_delta_of_sweepBlockDefect
        H N hN delta hDefect x
  have hGap :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkFullSweepMeanContraction_implies_transferGap
      H N hN 0 (by norm_num) q hq0 hq1 hContract
  have hCoeff :
      3 * (1 - q) / 8 =
        3 * ((1 / 6 : ℝ) - delta) / 8 := by
    dsimp [q]
    ring
  rw [← hCoeff]
  exact hGap

/-- Strict positivity form of the preceding quantitative receiver. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPhysicalSixSpatial_sweepBlockDefectMargin_positive_transferGap
    (delta : ℝ)
    (hdelta0 : 0 ≤ delta)
    (hdelta : delta < 1 / 6)
    (hDefect :
      ∀ x : K0,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepBlockDefectMeanNormSq
            H N hN 0 (by norm_num)
            (R0 (U0 ((x : G) : HaarL2))) ≤
          delta * ‖(x : G)‖ ^ 2) :
    0 <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
        H N hN 0 (by norm_num) := by
  have hGap :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPhysicalSixSpatial_sweepBlockDefectMargin_implies_transferGap
      H N hN delta hdelta0 hdelta hDefect
  have hMargin : 0 < (1 / 6 : ℝ) - delta := by
    linarith
  have hPos :
      0 < 3 * ((1 / 6 : ℝ) - delta) / 8 :=
    div_pos (mul_pos (by norm_num) hMargin) (by norm_num)
  exact lt_of_lt_of_le hPos hGap

end FiniteVolume

end

end MGAP4D.MathlibAnalytic
