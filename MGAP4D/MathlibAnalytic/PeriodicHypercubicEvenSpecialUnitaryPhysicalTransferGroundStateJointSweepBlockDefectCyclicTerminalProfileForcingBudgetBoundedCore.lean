import MGAP4D.MathlibAnalytic.RealHilbertProjectionSweepTargetResidualForcingBudgetTrajectory
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepBlockDefectCyclicTerminalProfileForcingBudget
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepBlockDefectCyclicSourceStepProfileClassification
import Mathlib.Tactic

/-!
# Domain-correct cyclic terminal forcing on the bounded concrete core

PR #4921 has an ambient, universal one-step hypothesis. Actual source-update
analysis has bounded-concrete and off-diagonal hypotheses instead. These are
not interchangeable quantifiers.

The first theorem compares the existing physical receiver's exact residual
increment budget with an analytic budget only along the actual suffix ++ pre
trajectory. The second supplies these stages using existing bounded-core
invariance and the exact cyclic source-set theorem. Its analytic hypothesis is
needed only for bounded-core vectors and source.val != target.val.

This closes the domain adapter, not the analytic beta-small forcing estimate.
No commutator coefficient is replaced by a source residual, no kernel is
identified with another kernel, and no positive-beta gap is claimed.
-/

namespace MGAP4D.MathlibAnalytic

noncomputable section

local instance cyclicTerminalForcingBoundedCoreSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

/-- Only actual before-source vectors need satisfy the analytic step estimate.
The original physical terminal receiver and its budget are reused unchanged. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile_le_cyclicForcingBudget_of_trajectory
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (pre suffix : List (PeriodicHypercubicEvenFixedSpatialColorLink H color))
    (target : PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta)
    (hSplit : (Finset.univ : Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList =
      pre ++ target :: suffix)
    (forcing : PeriodicHypercubicEvenFixedSpatialColorLink H color →
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta → ℝ)
    (hStep :
      let P :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color
      let x0 := P target (realHilbertProjectionSweep P pre f)
      ∀ (before : List (PeriodicHypercubicEvenFixedSpatialColorLink H color))
        (source : PeriodicHypercubicEvenFixedSpatialColorLink H color)
        (after : List (PeriodicHypercubicEvenFixedSpatialColorLink H color)),
        suffix ++ pre = before ++ source :: after →
        ‖P source (realHilbertProjectionSweep P before x0) -
            P target (P source (realHilbertProjectionSweep P before x0))‖ ≤
          forcing source (realHilbertProjectionSweep P before x0) +
            ‖realHilbertProjectionSweep P before x0 -
              P target (realHilbertProjectionSweep P before x0)‖) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile
        H N hN beta hbeta color f target ≤
      realHilbertProjectionSweepTargetResidualForcingBudget
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color) forcing (suffix ++ pre)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color target
          (realHilbertProjectionSweep
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
              H N hN beta hbeta color) pre f)) := by
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
      H N hN beta hbeta color
  let x0 := P target (realHilbertProjectionSweep P pre f)
  let increment : PeriodicHypercubicEvenFixedSpatialColorLink H color →
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta → ℝ :=
    fun source x => ‖P source x - P target (P source x)‖ - ‖x - P target x‖
  have hExact : ∀ (source : PeriodicHypercubicEvenFixedSpatialColorLink H color)
      (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta),
      ‖P source x - P target (P source x)‖ ≤ increment source x + ‖x - P target x‖ := by
    intro source x
    exact le_of_eq (sub_add_cancel _ _).symm
  have hTerminal :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile_le_cyclicForcingBudget
      H N hN beta hbeta color pre suffix target f hSplit increment hExact
  have hBudget :=
    realHilbertProjectionSweepTargetResidualForcingBudget_mono_on_trajectory
      P increment forcing (suffix ++ pre) x0 (by
        intro before source after hCyclicSplit
        exact (sub_le_iff_le_add).2 (hStep before source after hCyclicSplit))
  exact hTerminal.trans hBudget

/-- Bounded-core, off-diagonal analytic input is sufficient. The ambient L2
space is not used as the quantifier domain of the analytic hypothesis. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile_le_cyclicForcingBudget_of_boundedCore
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (pre suffix : List (PeriodicHypercubicEvenFixedSpatialColorLink H color))
    (target : PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta)
    (hf : f ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
        H N hN beta hbeta)
    (hSplit : (Finset.univ : Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList =
      pre ++ target :: suffix)
    (forcing : PeriodicHypercubicEvenFixedSpatialColorLink H color →
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta → ℝ)
    (hStep :
      let P :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color
      ∀ (source : PeriodicHypercubicEvenFixedSpatialColorLink H color),
        source.1 ≠ target.1 →
        ∀ (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta),
          x ∈ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
            H N hN beta hbeta →
          ‖P source x - P target (P source x)‖ ≤ forcing source x + ‖x - P target x‖) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile
        H N hN beta hbeta color f target ≤
      realHilbertProjectionSweepTargetResidualForcingBudget
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color) forcing (suffix ++ pre)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color target
          (realHilbertProjectionSweep
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
              H N hN beta hbeta color) pre f)) := by
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
      H N hN beta hbeta color
  let x0 := P target (realHilbertProjectionSweep P pre f)
  have hPre : realHilbertProjectionSweep P pre f ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
        H N hN beta hbeta := by
    simpa only [P] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweep_mem_boundedConcreteCore
        H N hN beta hbeta color pre f hf
  have hStart : x0 ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
        H N hN beta hbeta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2_mem_boundedConcreteCore
      H N hN beta hbeta color target (realHilbertProjectionSweep P pre f) hPre
  have hFresh : target ∉ pre :=
    periodicHypercubicEvenFixedSpatialColorLink_canonicalSplit_fresh
      H color pre suffix target hSplit
  apply
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile_le_cyclicForcingBudget_of_trajectory
      H N hN beta hbeta color pre suffix target f hSplit forcing
  change ∀ (before : List (PeriodicHypercubicEvenFixedSpatialColorLink H color))
    (source : PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (after : List (PeriodicHypercubicEvenFixedSpatialColorLink H color)),
    suffix ++ pre = before ++ source :: after →
    ‖P source (realHilbertProjectionSweep P before x0) -
        P target (P source (realHilbertProjectionSweep P before x0))‖ ≤
      forcing source (realHilbertProjectionSweep P before x0) +
        ‖realHilbertProjectionSweep P before x0 -
          P target (realHilbertProjectionSweep P before x0)‖
  intro before source after hCyclicSplit
  have hBefore : realHilbertProjectionSweep P before x0 ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
        H N hN beta hbeta := by
    simpa only [P] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweep_mem_boundedConcreteCore
        H N hN beta hbeta color before x0 hStart
  have hMem : source ∈ suffix ++ pre := by
    rw [hCyclicSplit]
    simp only [List.mem_append, List.mem_cons, eq_self_iff_true, true_or, or_true]
  have hne : source.1 ≠ target.1 :=
    periodicHypercubicEvenFixedSpatialColorLink_cyclicBetweenVisits_source_ne_target
      H color pre suffix target source hSplit hFresh hMem
  exact hStep source hne (realHilbertProjectionSweep P before x0) hBefore

end

end MGAP4D.MathlibAnalytic
