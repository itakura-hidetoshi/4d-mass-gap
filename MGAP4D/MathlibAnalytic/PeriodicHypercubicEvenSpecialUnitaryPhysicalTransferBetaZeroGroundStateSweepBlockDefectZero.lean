import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroGroundStateSameColorOneLinkSweepEqualsColorBlock
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroGroundStateSameColorOneLinkSweepPairHaarTransport
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroGroundStateFullSweepDefectMargin
import Mathlib.Tactic

/-!
# Exact beta-zero sweep--block defect zero

The beta-zero genuine same-color one-link full sweep and the genuine
spatial-color conditional expectation become, after the exact joint-to-pair-Haar
measure cast,

* the literal pair-Haar same-color one-link sweep; and
* the literal pair-Haar spatial-color projection.

The preceding unit proves those literal pair-Haar operators are identical.
Because the measure cast is injective, the genuine beta-zero operators agree
pointwise.  Consequently every sweep--block defect vector vanishes, the
six-color mean defect energy is exactly zero, and the defect-margin receiver
may be instantiated with delta = 0.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped BigOperators InnerProductSpace InnerProduct

noncomputable section

local instance betaZeroSweepBlockDefectZeroTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance betaZeroSweepBlockDefectZeroCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance betaZeroSweepBlockDefectZeroSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance betaZeroSweepBlockDefectZeroMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance betaZeroSweepBlockDefectZeroBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance betaZeroSweepBlockDefectZeroSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Exact L2 casts along equality of measures are injective. -/
theorem realL2CastOfMeasureEq_injective
    {α : Type*}
    [MeasurableSpace α]
    {μ ν : Measure α}
    (hμν : μ = ν) :
    Function.Injective (realL2CastOfMeasureEq hμν) := by
  cases hμν
  intro f g h
  simpa using h

/-- The canonical beta-zero joint-to-pair-Haar cast is injective. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2_injective
    (H N : ℕ)
    (hN : 0 < N) :
    Function.Injective
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2
        H N hN) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2
  exact
    realL2CastOfMeasureEq_injective
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_zero_eq_pairHaar
        H N hN)

/-- At beta zero, the genuine complete same-color one-link sweep is exactly the
genuine spatial-color conditional expectation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZero_fixedSpatialColor_fullOneLinkSweep_eq_colorCondExp
    (H N : ℕ)
    (hN : 0 < N)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (z :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN 0 (by norm_num)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
        H N hN 0 (by norm_num) color z =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
        H N hN 0 (by norm_num) color z := by
  let J :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2
      H N hN
  let c := periodicHypercubicEvenGroundStateSpatialColorEquivFin color
  have hSweep :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2_fixedSpatialColor_fullOneLinkSweep
      H N hN color z
  have hPairOp :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkPairHaarFullSweep_eq_colorProjection
      H N color
  have hPairApply := congrArg
    (fun T :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N =>
      T (J z))
    hPairOp
  have hColor0 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2_sixSpatialCondExp
      H N hN c z
  have hColor :
      J
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
            H N hN 0 (by norm_num) color z) =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorPairHaarProjection
          H N color (J z) := by
    simpa [
      J, c,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection] using
      hColor0
  apply
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2_injective
      H N hN
  calc
    J
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
          H N hN 0 (by norm_num) color z) =
      realHilbertProjectionSweep
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkPairHaarProjection
          H N color)
        ((Finset.univ :
          Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList)
        (J z) := by
          simpa [J] using hSweep
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorPairHaarProjection
        H N color (J z) := by
          simpa only [ContinuousLinearMap.comp_apply] using hPairApply
    _ =
      J
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
          H N hN 0 (by norm_num) color z) :=
      hColor.symm

/-- Every beta-zero fixed-color sweep--block defect vector vanishes exactly. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZero_fixedSpatialColorOneLinkSweepBlockDefectVector_eq_zero
    (H N : ℕ)
    (hN : 0 < N)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (z :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN 0 (by norm_num)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
        H N hN 0 (by norm_num) color z = 0 := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZero_fixedSpatialColor_fullOneLinkSweep_eq_colorCondExp
      H N hN color z]
  exact sub_self _

/-- The six-spatial beta-zero mean sweep--block defect energy is exactly zero
on every genuine joint L2 vector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZero_sixSpatialOneLinkSweepBlockDefectMeanNormSq_eq_zero
    (H N : ℕ)
    (hN : 0 < N)
    (z :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN 0 (by norm_num)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepBlockDefectMeanNormSq
        H N hN 0 (by norm_num) z = 0 := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepBlockDefectMeanNormSq
  simp [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZero_fixedSpatialColorOneLinkSweepBlockDefectVector_eq_zero
      H N hN]

/-- At beta zero, the complete one-link full-sweep mean norm is exactly the
genuine six-spatial mean projected norm. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZero_sixSpatialOneLinkFullSweepMeanNormSq_eq_meanProjectedNormSq
    (H N : ℕ)
    (hN : 0 < N)
    (z :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN 0 (by norm_num)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkFullSweepMeanNormSq
        H N hN 0 (by norm_num) z =
      groundStateJointColorMeanProjectedNormSq
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2
          H N hN 0 (by norm_num))
        z := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkFullSweepMeanNormSq_eq_meanProjectedNormSq_add_sweepBlockDefectMeanNormSq,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZero_sixSpatialOneLinkSweepBlockDefectMeanNormSq_eq_zero
      H N hN z,
    add_zero]

section Physical

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

/-- The beta-zero complete same-color one-link full sweeps have the exact
physical contraction coefficient 5/6. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPhysicalSixSpatialFullSweepMean_five_six
    (x : K0) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkFullSweepMeanNormSq
        H N hN 0 (by norm_num)
        (R0 (U0 ((x : G) : HaarL2))) ≤
      (5 / 6 : ℝ) * ‖(x : G)‖ ^ 2 := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZero_sixSpatialOneLinkFullSweepMeanNormSq_eq_meanProjectedNormSq
      H N hN]
  have hMean :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPhysicalSixSpatialMeanProjection_five_six
      H N hN x
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialMeanProjectedNormSq] using
    hMean

/-- The beta-zero defect-margin hypothesis holds with the exact coefficient
delta = 0. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPhysicalSixSpatial_sweepBlockDefect_zero_majorant :
    ∀ x : K0,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepBlockDefectMeanNormSq
          H N hN 0 (by norm_num)
          (R0 (U0 ((x : G) : HaarL2))) ≤
        (0 : ℝ) * ‖(x : G)‖ ^ 2 := by
  intro x
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZero_sixSpatialOneLinkSweepBlockDefectMeanNormSq_eq_zero
      H N hN]
  norm_num

/-- Instantiating the defect-margin receiver with delta = 0 gives the explicit
receiver lower bound 1/16 for the beta-zero physical transfer gap.  The
separately proved exact beta-zero gap = 1 remains strictly stronger. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPhysicalSixSpatial_zeroSweepBlockDefect_receiver_transferGap :
    (1 / 16 : ℝ) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
        H N hN 0 (by norm_num) := by
  have hGap :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPhysicalSixSpatial_sweepBlockDefectMargin_implies_transferGap
      H N hN
      0
      (by norm_num)
      (by norm_num)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPhysicalSixSpatial_sweepBlockDefect_zero_majorant
        H N hN)
  norm_num at hGap
  exact hGap

end Physical

end

end MGAP4D.MathlibAnalytic
