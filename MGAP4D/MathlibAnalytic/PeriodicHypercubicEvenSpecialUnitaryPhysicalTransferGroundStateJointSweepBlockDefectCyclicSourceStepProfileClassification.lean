import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepBlockDefectCyclicSourceStepQuantitative
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepStageLocalProfileExactResidual
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepBlockDefectTerminalProfileRenewal
import Mathlib.Tactic

/-!
# Exact profile classification of cyclic between-visits source steps

Fix a canonical target split

  canonicalList = pre ++ target :: suffix.

The cyclic order between the first and second visits to the target is

  suffix ++ pre.

There are therefore exactly two kinds of source step.

* A source lying in `suffix` is still part of the first sweep.  Its exact
  cyclic stage-residual energy is the square of the original local profile.
* A source lying in `pre` is visited only after the first sweep has
  completed.  Its exact cyclic stage-residual energy is the square of the
  terminal local profile.

This file proves both identities exactly.  It reuses the unique-stage theorem
from PR #4856 and the cyclic source-step carrier from PRs #4906--#4909.
No cross-link commutativity, response symmetry, cardinality estimate, or
coefficient weakening is used.
-/

namespace MGAP4D.MathlibAnalytic

noncomputable section

local instance cyclicSourceStepProfileClassificationSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Freshness is automatic for any displayed position in the canonical
duplicate-free fixed-color list. -/
theorem
    periodicHypercubicEvenFixedSpatialColorLink_canonicalSplit_fresh
    (H : ℕ)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (pre suffix :
      List (PeriodicHypercubicEvenFixedSpatialColorLink H color))
    (e : PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (hSplit :
      (Finset.univ :
        Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList =
          pre ++ e :: suffix) :
    e ∉ pre := by
  have hNodup : (pre ++ e :: suffix).Nodup := by
    rw [← hSplit]
    exact Finset.nodup_toList _
  have hMiddle : (e :: (pre ++ suffix)).Nodup :=
    (List.nodup_middle.mp hNodup)
  have hNot : e ∉ pre ++ suffix :=
    hMiddle.notMem
  intro he
  exact hNot (by simp [he])

/-- A cyclic source step that lies in the target suffix is exactly an original
first-sweep stage.  Hence its exact trajectory residual energy is the square
of the original fixed-color local profile at that source. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSecondVisitCyclicSourceStepResidualEnergy_eq_originalLocalProfile_sq_of_suffixSplit
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (pre suffix before after :
      List (PeriodicHypercubicEvenFixedSpatialColorLink H color))
    (target source :
      PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hCanonicalSplit :
      (Finset.univ :
        Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList =
          pre ++ target :: suffix)
    (hSuffixSplit :
      suffix = before ++ source :: after) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSecondVisitCyclicSourceStepResidualEnergy
        H N hN beta hbeta color pre before target source f =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageLocalProfile
        H N hN beta hbeta color f source ^ 2 := by
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
      H N hN beta hbeta color
  let x0 :=
    P target (realHilbertProjectionSweep P pre f)
  have hSourceSplit :
      (Finset.univ :
        Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList =
          (pre ++ target :: before) ++ source :: after := by
    rw [hCanonicalSplit, hSuffixSplit]
    simp [List.append_assoc]
  have hSourceFresh :
      source ∉ pre ++ target :: before :=
    periodicHypercubicEvenFixedSpatialColorLink_canonicalSplit_fresh
      H color (pre ++ target :: before) after source hSourceSplit
  have hProfile :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageLocalProfile_eq_stageResidual_norm_of_canonicalPrefix
      H N hN beta hbeta color
      (pre ++ target :: before) after source f
      hSourceSplit hSourceFresh
  have hStage :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
          H N hN beta hbeta color (pre ++ target :: before) f =
        realHilbertProjectionSweep P before x0 := by
    change
      realHilbertProjectionSweep P (pre ++ target :: before) f =
        realHilbertProjectionSweep P before x0
    rw [realHilbertProjectionSweep_append P pre (target :: before) f]
    rfl
  have hProfile' :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageLocalProfile
          H N hN beta hbeta color f source =
        ‖realHilbertProjectionSweep P before x0 -
          P source (realHilbertProjectionSweep P before x0)‖ := by
    rw [hProfile, hStage]
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSecondVisitCyclicSourceStepResidualEnergy
        H N hN beta hbeta color pre before target source f =
      ‖realHilbertProjectionSweep P before x0 -
          P source (realHilbertProjectionSweep P before x0)‖ ^ 2 := by
            unfold
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSecondVisitCyclicSourceStepResidualEnergy
            change
              ‖realHilbertProjectionSweep P before x0 -
                realHilbertProjectionSweep P (before ++ [source]) x0‖ ^ 2 =
                _
            rw [realHilbertProjectionSweep_append P before [source] x0]
            rfl
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageLocalProfile
        H N hN beta hbeta color f source ^ 2 := by
          rw [hProfile']

/-- A cyclic source step that lies in the target prefix is visited only after
the first sweep has completed.  Hence its exact trajectory residual energy is
the square of the terminal fixed-color local profile at that source. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSecondVisitCyclicSourceStepResidualEnergy_eq_terminalLocalProfile_sq_of_preSplit
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (pre suffix before after :
      List (PeriodicHypercubicEvenFixedSpatialColorLink H color))
    (target source :
      PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hCanonicalSplit :
      (Finset.univ :
        Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList =
          pre ++ target :: suffix)
    (hPreSplit :
      pre = before ++ source :: after) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSecondVisitCyclicSourceStepResidualEnergy
        H N hN beta hbeta color pre (suffix ++ before) target source f =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile
        H N hN beta hbeta color f source ^ 2 := by
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
      H N hN beta hbeta color
  let x0 :=
    P target (realHilbertProjectionSweep P pre f)
  have hSourceSplit :
      (Finset.univ :
        Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList =
          before ++ source :: (after ++ target :: suffix) := by
    rw [hCanonicalSplit, hPreSplit]
    simp [List.append_assoc]
  have hSourceFresh :
      source ∉ before :=
    periodicHypercubicEvenFixedSpatialColorLink_canonicalSplit_fresh
      H color before (after ++ target :: suffix) source hSourceSplit
  have hProfile :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageLocalProfile_eq_stageResidual_norm_of_canonicalPrefix
      H N hN beta hbeta color
      before (after ++ target :: suffix) source
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
        H N hN beta hbeta color f)
      hSourceSplit hSourceFresh
  have hTerminalProfile :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile
          H N hN beta hbeta color f source =
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
            H N hN beta hbeta color before
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
              H N hN beta hbeta color f) -
          P source
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
              H N hN beta hbeta color before
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
                H N hN beta hbeta color f))‖ := by
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile
    simpa [P] using hProfile
  have hFull :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
          H N hN beta hbeta color f =
        realHilbertProjectionSweep P suffix x0 := by
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
    change
      realHilbertProjectionSweep P
          ((Finset.univ :
            Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList) f =
        realHilbertProjectionSweep P suffix x0
    rw [hCanonicalSplit]
    rw [realHilbertProjectionSweep_append P pre (target :: suffix) f]
    rfl
  have hStage :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
          H N hN beta hbeta color before
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
            H N hN beta hbeta color f) =
        realHilbertProjectionSweep P (suffix ++ before) x0 := by
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
    rw [hFull]
    rw [realHilbertProjectionSweep_append P suffix before x0]
  have hTerminalProfile' :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile
          H N hN beta hbeta color f source =
        ‖realHilbertProjectionSweep P (suffix ++ before) x0 -
          P source (realHilbertProjectionSweep P (suffix ++ before) x0)‖ := by
    rw [hTerminalProfile, hStage]
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSecondVisitCyclicSourceStepResidualEnergy
        H N hN beta hbeta color pre (suffix ++ before) target source f =
      ‖realHilbertProjectionSweep P (suffix ++ before) x0 -
          P source (realHilbertProjectionSweep P (suffix ++ before) x0)‖ ^ 2 := by
            unfold
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSecondVisitCyclicSourceStepResidualEnergy
            change
              ‖realHilbertProjectionSweep P (suffix ++ before) x0 -
                realHilbertProjectionSweep P ((suffix ++ before) ++ [source]) x0‖ ^ 2 =
                _
            rw [realHilbertProjectionSweep_append P (suffix ++ before) [source] x0]
            rfl
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile
        H N hN beta hbeta color f source ^ 2 := by
          rw [hTerminalProfile']

end

end MGAP4D.MathlibAnalytic
