import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepBlockDefectRenewal
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointFixedColorSweepVectorTelescoping
import Mathlib.Tactic

/-!
# Vector renewal for the positive-beta sweep--block defect

PR #4892 proves the squared-norm renewal law

  ||D_c(f)||^2 = L_c(S_c f) + ||D_c(S_c f)||^2.

For the next response step we need the exact vector carrier behind that energy
identity.  This file exposes it without introducing any estimate.

Let

* `S_c` be the complete canonical one-link sweep of one fixed spatial color;
* `D_c(f) = S_c f - B_c f` be the sweep--block defect vector;
* `R_c(x)` be the canonical sum of all one-link residual vectors generated
  while sweeping `x`.

Then

  D_c(f) = R_c(S_c f) + D_c(S_c f).

Moreover, if the canonical list is split as

  canonicalList = pre ++ e :: suffix,

the second-sweep residual carrier is exposed exactly as

  prefix residual sum
    + e-stage residual
    + suffix residual sum.

This is the semantic bridge needed before identifying suffix-generated
recontamination with the backward source-update response machinery of
PRs #4876--#4878.

No commutativity, response symmetry, finite-cardinality estimate, or new
coefficient is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped BigOperators InnerProductSpace InnerProduct

noncomputable section

local instance sweepBlockDefectVectorRenewalSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance sweepBlockDefectVectorRenewalSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Exact vector renewal behind the PR #4892 energy identity:
the present sweep--block defect equals the full residual-vector sum generated
by sweeping the terminal vector once more, plus the next sweep--block defect. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector_eq_terminalSweepResidualVectorSum_add_nextDefectVector
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
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepResidualVectorSum
          H N hN beta hbeta color
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
            H N hN beta hbeta color f) +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
          H N hN beta hbeta color
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
            H N hN beta hbeta color f) := by
  let B :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
      H N hN beta hbeta color
  let S :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
      H N hN beta hbeta color f
  let S2 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
      H N hN beta hbeta color S
  have hAbsorb : B S = B f := by
    simpa [B, S] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2_fullOneLinkSweep_eq
        H N hN beta hbeta color f
  have hResidual :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepResidualVectorSum_eq_sub_fullSweep
      H N hN beta hbeta color S
  have hResidual' :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepResidualVectorSum
          H N hN beta hbeta color S =
        S - S2 := by
    simpa [
      S2,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector] using
      hResidual
  change
    S - B f =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepResidualVectorSum
          H N hN beta hbeta color S +
        (S2 - B S)
  rw [hResidual', ← hAbsorb]
  abel

/-- Difference form of the vector renewal:
the complete second-sweep residual-vector sum is exactly the amount removed
from the current defect vector before the next defect remains. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColor_terminalSweepResidualVectorSum_eq_defectVector_sub_nextDefectVector
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepResidualVectorSum
        H N hN beta hbeta color
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
          H N hN beta hbeta color f) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
          H N hN beta hbeta color f -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
          H N hN beta hbeta color
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
            H N hN beta hbeta color f) := by
  have hRenew :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector_eq_terminalSweepResidualVectorSum_add_nextDefectVector
      H N hN beta hbeta color f
  rw [hRenew]
  abel

/-- Canonical stage/suffix exposure of the vector renewal.

If the canonical color list is `pre ++ e :: suffix`, then the current defect
is exactly the sum of

* second-sweep residuals before `e`;
* the exact residual at the `e)-stage;
* second-sweep residuals generated by the canonical suffix after `e`;
* the next sweep--block defect.

The suffix term is the exact carrier to be matched to backward source-update
responses in the following step. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector_eq_terminalPrefix_add_stageResidual_add_suffix_add_nextDefectVector
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (pre suffix :
      List (PeriodicHypercubicEvenFixedSpatialColorLink H color))
    (e : PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hSplit :
      (Finset.univ :
        Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList =
          pre ++ e :: suffix) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
        H N hN beta hbeta color f =
      realHilbertProjectionSweepResidualVectorSum
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
            H N hN beta hbeta color)
          pre
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
            H N hN beta hbeta color f) +
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
              H N hN beta hbeta color pre
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
                H N hN beta hbeta color f) -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
              H N hN beta hbeta color e
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
                H N hN beta hbeta color pre
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
                  H N hN beta hbeta color f))) +
          realHilbertProjectionSweepResidualVectorSum
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
              H N hN beta hbeta color)
            suffix
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
              H N hN beta hbeta color e
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
                H N hN beta hbeta color pre
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
                  H N hN beta hbeta color f)))) +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
          H N hN beta hbeta color
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
            H N hN beta hbeta color f) := by
  let S :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
      H N hN beta hbeta color f
  have hRenew :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector_eq_terminalSweepResidualVectorSum_add_nextDefectVector
      H N hN beta hbeta color f
  have hStage :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepResidualVectorSum_eq_prefix_add_stageResidual_add_suffix
      H N hN beta hbeta color pre suffix e S hSplit
  rw [hStage] at hRenew
  simpa [S] using hRenew

end

end MGAP4D.MathlibAnalytic
