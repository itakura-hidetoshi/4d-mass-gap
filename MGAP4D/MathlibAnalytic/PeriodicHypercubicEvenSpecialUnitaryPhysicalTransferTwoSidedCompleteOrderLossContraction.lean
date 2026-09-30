import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedLossContraction
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepStageLocalProfileExactResidual
import Mathlib.Tactic

/-!
# Two-sided loss contraction for any complete duplicate-free tagged-link order

The #4969 theorem is stated for the canonical `Finset.univ.toList` order.
For the volume-free twelve-color grouping step we must not silently reorder
noncommuting conditional expectations.

This file proves the order-robust form needed by G1.  For any finite tagged
two-sided link list which

* contains every tagged link, and
* is duplicate-free,

the same two-boundary ordered Schur coefficient gives the same strict path-loss
contraction.  No link-count, lattice-volume, rank, or permutation coefficient
is introduced.

The proof reuses the already-closed #4967 cyclic forcing estimate.  The only
new bookkeeping is to split the supplied complete list at each target and to
identify the first- and second-sweep stage profiles relative to that exact
order.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section

local instance twoSidedCompleteOrderLossSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Stage-residual amplitude profile for an explicitly supplied two-sided order. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfileFor
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (sources : List (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H))
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H → ℝ :=
  realHilbertProjectionSweepStageResidualAmplitude
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
      H N hN beta hbeta)
    sources f

/-- The second-sweep stage profile for the same explicitly supplied order. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkTerminalSweepStageLocalProfileFor
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (sources : List (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H))
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H → ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfileFor
    H N hN beta hbeta sources
    (realHilbertProjectionSweep
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
        H N hN beta hbeta)
      sources f)

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfileFor_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (sources : List (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H))
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (source : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfileFor
        H N hN beta hbeta sources f source :=
  realHilbertProjectionSweepStageResidualAmplitude_nonneg
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
      H N hN beta hbeta)
    sources f source

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkTerminalSweepStageLocalProfileFor_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (sources : List (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H))
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (source : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkTerminalSweepStageLocalProfileFor
        H N hN beta hbeta sources f source := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfileFor_nonneg
      H N hN beta hbeta sources
      (realHilbertProjectionSweep
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
          H N hN beta hbeta)
        sources f)
      source

/-- Exact path-loss identity for the supplied order. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfileFor_sq_sum_eq_pathLoss
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (sources : List (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H))
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    (∑ source : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfileFor
        H N hN beta hbeta sources f source ^ 2) =
      realHilbertProjectionSweepPathLoss
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
          H N hN beta hbeta)
        sources f := by
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfileFor] using
    realHilbertProjectionSweepStageResidualAmplitude_sq_sum_eq_pathLoss
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
        H N hN beta hbeta)
      sources f

/-- Freshness of a displayed position in an arbitrary duplicate-free order. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_completeOrderSplit_fresh
    (H : ℕ)
    (sources pre suffix :
      List (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H))
    (target : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H)
    (hNodup : sources.Nodup)
    (hSplit : sources = pre ++ target :: suffix) :
    target ∉ pre := by
  have hDisplayed : (pre ++ target :: suffix).Nodup := by
    rw [← hSplit]
    exact hNodup
  have hMiddle : (target :: (pre ++ suffix)).Nodup :=
    List.nodup_middle.mp hDisplayed
  have hNot : target ∉ pre ++ suffix :=
    hMiddle.notMem
  intro ht
  exact hNot (by simp [ht])

/-- At a displayed position of a duplicate-free supplied order, the profile is
exactly the genuine residual norm at that prefix stage. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfileFor_eq_stageResidual_norm_of_split
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (sources pre suffix :
      List (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H))
    (source : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hNodup : sources.Nodup)
    (hSplit : sources = pre ++ source :: suffix) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfileFor
        H N hN beta hbeta sources f source =
      ‖realHilbertProjectionSweep
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
            H N hN beta hbeta)
          pre f -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
          H N hN beta hbeta source
          (realHilbertProjectionSweep
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
              H N hN beta hbeta)
            pre f)‖ := by
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
      H N hN beta hbeta
  have hFresh :
      source ∉ pre :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_completeOrderSplit_fresh
      H sources pre suffix source hNodup hSplit
  have hDisplayed : (pre ++ source :: suffix).Nodup := by
    rw [← hSplit]
    exact hNodup
  have hTailNodup : (source :: suffix).Nodup :=
    hDisplayed.of_append_right
  have hSuffix : source ∉ suffix :=
    (List.nodup_cons.mp hTailNodup).1
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfileFor
  rw [hSplit]
  exact
    realHilbertProjectionSweepStageResidualAmplitude_append_cons_eq_norm
      P pre suffix f source hFresh hSuffix

/-- Pointwise terminal recurrence for any complete duplicate-free tagged-link
order.  The coefficient is exactly the existing two-boundary ordered kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_terminalProfileFor_le_ordered_forcing_feedback
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (hs : 1 < s)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (hBetaLt :
      beta <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBetaThreshold)
    (sources : List (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H))
    (hNodup : sources.Nodup)
    (hComplete :
      ∀ source : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H,
        source ∈ sources)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hf :
      f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta)
    (target : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkTerminalSweepStageLocalProfileFor
        H N hN beta hbeta sources f target ≤
      (∑ source : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H,
        GroundStateSourceFixedPairEnergy.twoBoundaryOrderedKernel
            H N hN beta hbeta s target source *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfileFor
            H N hN beta hbeta sources f source) +
        ∑ source : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H,
          GroundStateSourceFixedPairEnergy.twoBoundaryOrderedKernel
              H N hN beta hbeta s target source *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkTerminalSweepStageLocalProfileFor
              H N hN beta hbeta sources f source := by
  classical
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
      H N hN beta hbeta
  let K :=
    GroundStateSourceFixedPairEnergy.twoBoundaryOrderedKernel
      H N hN beta hbeta s
  let O :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfileFor
      H N hN beta hbeta sources f
  let Full := realHilbertProjectionSweep P sources f
  let T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkTerminalSweepStageLocalProfileFor
      H N hN beta hbeta sources f
  obtain ⟨pre, suffix, hSplit⟩ :=
    List.mem_iff_append.mp (hComplete target)
  let x0 := P target (realHilbertProjectionSweep P pre f)
  let forcing :
      PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H →
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta → ℝ :=
    fun source y => K target source * ‖y - P source y‖
  have hCyclic :
      ‖realHilbertProjectionSweep P (suffix ++ pre) x0 -
          P target (realHilbertProjectionSweep P (suffix ++ pre) x0)‖ ≤
        realHilbertProjectionSweepTargetResidualForcingBudget
          P forcing (suffix ++ pre) x0 := by
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_cyclicTargetResidual_norm_le_orderedForcingBudget
        H N hN beta hbeta s hs hcut hBetaLt pre suffix target f hf
  have hFull :
      Full = realHilbertProjectionSweep P suffix x0 := by
    dsimp [Full]
    rw [hSplit]
    rw [realHilbertProjectionSweep_append P pre (target :: suffix) f]
    rfl
  have hTerminalStage :
      realHilbertProjectionSweep P pre Full =
        realHilbertProjectionSweep P (suffix ++ pre) x0 := by
    rw [hFull]
    rw [realHilbertProjectionSweep_append P suffix pre x0]
  have hTerminalProfile :
      T target =
        ‖realHilbertProjectionSweep P (suffix ++ pre) x0 -
          P target (realHilbertProjectionSweep P (suffix ++ pre) x0)‖ := by
    have hProfile :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfileFor_eq_stageResidual_norm_of_split
        H N hN beta hbeta sources pre suffix target Full hNodup hSplit
    change
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfileFor
          H N hN beta hbeta sources Full target =
        ‖realHilbertProjectionSweep P (suffix ++ pre) x0 -
          P target (realHilbertProjectionSweep P (suffix ++ pre) x0)‖
    rw [hProfile, hTerminalStage]
  have hDisplayed : (pre ++ target :: suffix).Nodup := by
    rw [← hSplit]
    exact hNodup
  have hPreNodup : pre.Nodup :=
    hDisplayed.of_append_left
  have hTailNodup : (target :: suffix).Nodup :=
    hDisplayed.of_append_right
  have hSuffixNodup : suffix.Nodup :=
    hTailNodup.of_cons
  have hSuffixBudget :
      realHilbertProjectionSweepTargetResidualForcingBudget
          P forcing suffix x0 =
        ∑ source ∈ suffix.toFinset, K target source * O source := by
    apply
      realHilbertProjectionSweepTargetResidualForcingBudget_eq_sum_of_trajectory
        P forcing (fun source => K target source * O source)
        suffix x0 hSuffixNodup
    intro before source after hSuffixSplit
    have hSourceSplit :
        sources =
          (pre ++ target :: before) ++ source :: after := by
      rw [hSplit, hSuffixSplit]
      simp [List.append_assoc]
    have hProfile :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfileFor_eq_stageResidual_norm_of_split
        H N hN beta hbeta sources
        (pre ++ target :: before) after source f hNodup hSourceSplit
    have hStage :
        realHilbertProjectionSweep P (pre ++ target :: before) f =
          realHilbertProjectionSweep P before x0 := by
      rw [realHilbertProjectionSweep_append P pre (target :: before) f]
      rfl
    have hNorm :
        ‖realHilbertProjectionSweep P before x0 -
            P source (realHilbertProjectionSweep P before x0)‖ =
          O source := by
      change _ =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfileFor
          H N hN beta hbeta sources f source
      rw [hProfile, hStage]
    exact congrArg (fun a : ℝ => K target source * a) hNorm
  have hPreBudget :
      realHilbertProjectionSweepTargetResidualForcingBudget
          P forcing pre (realHilbertProjectionSweep P suffix x0) =
        ∑ source ∈ pre.toFinset, K target source * T source := by
    apply
      realHilbertProjectionSweepTargetResidualForcingBudget_eq_sum_of_trajectory
        P forcing (fun source => K target source * T source)
        pre (realHilbertProjectionSweep P suffix x0) hPreNodup
    intro before source after hPreSplit
    have hSourceSplit :
        sources =
          before ++ source :: (after ++ target :: suffix) := by
      rw [hSplit, hPreSplit]
      simp [List.append_assoc]
    have hProfile :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfileFor_eq_stageResidual_norm_of_split
        H N hN beta hbeta sources
        before (after ++ target :: suffix) source Full hNodup hSourceSplit
    have hNorm :
        ‖realHilbertProjectionSweep P before
              (realHilbertProjectionSweep P suffix x0) -
            P source
              (realHilbertProjectionSweep P before
                (realHilbertProjectionSweep P suffix x0))‖ =
          T source := by
      change _ =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfileFor
          H N hN beta hbeta sources Full source
      rw [← hFull, hProfile]
    exact congrArg (fun a : ℝ => K target source * a) hNorm
  have hBudgetEq :
      realHilbertProjectionSweepTargetResidualForcingBudget
          P forcing (suffix ++ pre) x0 =
        (∑ source ∈ suffix.toFinset, K target source * O source) +
          ∑ source ∈ pre.toFinset, K target source * T source := by
    rw [
      realHilbertProjectionSweepTargetResidualForcingBudget_append,
      hSuffixBudget,
      hPreBudget]
  have hRestricted :
      T target ≤
        (∑ source ∈ suffix.toFinset, K target source * O source) +
          ∑ source ∈ pre.toFinset, K target source * T source := by
    calc
      T target =
          ‖realHilbertProjectionSweep P (suffix ++ pre) x0 -
            P target (realHilbertProjectionSweep P (suffix ++ pre) x0)‖ :=
        hTerminalProfile
      _ ≤
          realHilbertProjectionSweepTargetResidualForcingBudget
            P forcing (suffix ++ pre) x0 := hCyclic
      _ =
          (∑ source ∈ suffix.toFinset, K target source * O source) +
            ∑ source ∈ pre.toFinset, K target source * T source :=
        hBudgetEq
  have hSuffixLe :
      (∑ source ∈ suffix.toFinset, K target source * O source) ≤
        ∑ source :
            PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H,
          K target source * O source :=
    Finset.sum_le_univ_sum_of_nonneg
      (fun source =>
        mul_nonneg
          (GroundStateSourceFixedPairEnergy.twoBoundaryOrderedKernel_nonneg
            H N hN beta hbeta s target source)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfileFor_nonneg
            H N hN beta hbeta sources f source))
  have hPreLe :
      (∑ source ∈ pre.toFinset, K target source * T source) ≤
        ∑ source :
            PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H,
          K target source * T source :=
    Finset.sum_le_univ_sum_of_nonneg
      (fun source =>
        mul_nonneg
          (GroundStateSourceFixedPairEnergy.twoBoundaryOrderedKernel_nonneg
            H N hN beta hbeta s target source)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkTerminalSweepStageLocalProfileFor_nonneg
            H N hN beta hbeta sources f source))
  exact hRestricted.trans (_root_.add_le_add hSuffixLe hPreLe)

/-- The same two-boundary Schur estimate controls the terminal profile for any
complete duplicate-free order. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_terminalProfileFor_energy_le_orderedSchur_feedback
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 8 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        GroundStateSourceFixedPairEnergy.twoBoundaryOrderedSchurCutoff s hs)
    (hBetaLt :
      beta <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBetaThreshold)
    (sources : List (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H))
    (hNodup : sources.Nodup)
    (hComplete :
      ∀ source : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H,
        source ∈ sources)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hf :
      f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta) :
    (1 -
        GroundStateSourceFixedPairEnergy.twoBoundaryOrderedSchurCoefficient
          s beta) ^ 2 *
        ∑ target : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkTerminalSweepStageLocalProfileFor
            H N hN beta hbeta sources f target ^ 2 ≤
      GroundStateSourceFixedPairEnergy.twoBoundaryOrderedSchurCoefficient
          s beta ^ 2 *
        ∑ source : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfileFor
            H N hN beta hbeta sources f source ^ 2 := by
  let matrix :=
    GroundStateSourceFixedPairEnergy.twoBoundaryOrderedKernel
      H N hN beta hbeta s
  let terminal :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkTerminalSweepStageLocalProfileFor
      H N hN beta hbeta sources f
  let original :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfileFor
      H N hN beta hbeta sources f
  let Q :=
    GroundStateSourceFixedPairEnergy.twoBoundaryOrderedSchurCoefficient s beta
  let forced :=
    fun target => ∑ source, matrix target source * original source
  have hJoint :
      beta ≤ GroundStateSourceFixedPairEnergy.jointLeakageSchurCutoff s hs :=
    hcut.trans
      (GroundStateSourceFixedPairEnergy.twoBoundaryOrderedSchurCutoff_le_jointLeakageSchurCutoff
        s hs)
  have hStrict :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s :=
    hJoint.trans
      (GroundStateSourceFixedPairEnergy.jointLeakageSchurCutoff_le_strictPhysicalSweepCutoff
        s hs)
  have hQ :
      0 ≤ Q ∧ Q < 1 :=
    GroundStateSourceFixedPairEnergy.twoBoundaryOrderedSchurCoefficient_nonneg_lt_one
      s hs beta hbeta hcut
  have hMatrix :
      ∀ target source, 0 ≤ matrix target source := by
    intro target source
    exact
      GroundStateSourceFixedPairEnergy.twoBoundaryOrderedKernel_nonneg
        H N hN beta hbeta s target source
  have hSchur :
      ∀ v : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H → ℝ,
        (∑ target,
          (∑ source, matrix target source * v source) ^ 2) ≤
        Q ^ 2 * ∑ source, v source ^ 2 := by
    intro v
    exact
      GroundStateSourceFixedPairEnergy.twoBoundaryOrderedKernel_action_sq_sum_le
        H N hN s hs beta hbeta hJoint v
  have hTerminal :
      ∀ target, 0 ≤ terminal target := by
    intro target
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkTerminalSweepStageLocalProfileFor_nonneg
        H N hN beta hbeta sources f target
  have hOriginal :
      ∀ source, 0 ≤ original source := by
    intro source
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfileFor_nonneg
        H N hN beta hbeta sources f source
  have hForced :
      ∀ target, 0 ≤ forced target := by
    intro target
    exact
      Finset.sum_nonneg
        (fun source _ =>
          mul_nonneg (hMatrix target source) (hOriginal source))
  have hRecurrence :
      ∀ target,
        terminal target ≤
          forced target +
            ∑ source, matrix target source * terminal source := by
    intro target
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_terminalProfileFor_le_ordered_forcing_feedback
        H N hN beta hbeta s (by linarith) hStrict hBetaLt
        sources hNodup hComplete f hf target
  have hCoercive :=
    FiniteSchurOneSidedProfile.global_energy_coercive
      matrix Q hQ.1 hQ.2 hMatrix hSchur
      terminal forced hTerminal hForced hRecurrence
  have hForceBound := hSchur original
  exact hCoercive.trans hForceBound

/-- On the bounded concrete core, every complete duplicate-free tagged-link
order contracts its own next-sweep path loss by the same exact ratio. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_pathLoss_le_lossRatio_mul_of_completeOrder
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossContractionCutoff
          s hs)
    (sources : List (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H))
    (hNodup : sources.Nodup)
    (hComplete :
      ∀ source : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H,
        source ∈ sources)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hf :
      f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta) :
    let P :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
        H N hN beta hbeta
    let S := realHilbertProjectionSweep P sources
    realHilbertProjectionSweepPathLoss P sources (S f) ≤
      GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossRatio s beta *
        realHilbertProjectionSweepPathLoss P sources f := by
  dsimp only
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
      H N hN beta hbeta
  let S := realHilbertProjectionSweep P sources
  let Q :=
    GroundStateSourceFixedPairEnergy.twoBoundaryOrderedSchurCoefficient s beta
  have hQ :=
    GroundStateSourceFixedPairEnergy.twoBoundaryOrderedSchurCoefficient_nonneg_lt_half
      s hs beta hbeta hcut
  have hDen : 0 < 1 - Q := by
    dsimp [Q]
    linarith [hQ.2]
  have hDenSq : 0 < (1 - Q) ^ 2 :=
    sq_pos_of_pos hDen
  have hEnergy :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_terminalProfileFor_energy_le_orderedSchur_feedback
      H N hN s hs beta hbeta
      (hcut.trans
        (GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossContractionCutoff_le_schurCutoff
          s hs))
      (GroundStateSourceFixedPairEnergy.beta_lt_crossThreshold_of_le_twoBoundaryOrderedLossContractionCutoff
        s hs beta hcut)
      sources hNodup hComplete f hf
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfileFor_sq_sum_eq_pathLoss
      H N hN beta hbeta sources (S f),
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfileFor_sq_sum_eq_pathLoss
      H N hN beta hbeta sources f] at hEnergy
  calc
    realHilbertProjectionSweepPathLoss P sources (S f) ≤
      (Q ^ 2 * realHilbertProjectionSweepPathLoss P sources f) / (1 - Q) ^ 2 :=
      (le_div_iff₀ hDenSq).2
        (by simpa only [mul_comm] using hEnergy)
    _ =
      GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossRatio s beta *
        realHilbertProjectionSweepPathLoss P sources f := by
      rw [
        GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossRatio,
        div_pow]
      ring

/-- Density/closedness extension of the complete-order loss contraction to all
vectors in the genuine joint L2 carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_pathLoss_le_lossRatio_mul_of_completeOrder_allL2
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossContractionCutoff
          s hs)
    (sources : List (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H))
    (hNodup : sources.Nodup)
    (hComplete :
      ∀ source : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H,
        source ∈ sources)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    let P :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
        H N hN beta hbeta
    let S := realHilbertProjectionSweep P sources
    realHilbertProjectionSweepPathLoss P sources (S f) ≤
      GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossRatio s beta *
        realHilbertProjectionSweepPathLoss P sources f := by
  dsimp only
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
      H N hN beta hbeta
  let S := realHilbertProjectionSweep P sources
  let eta :=
    GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossRatio s beta
  let loss :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta → ℝ :=
    fun g => ‖g‖ ^ 2 - ‖S g‖ ^ 2
  have hLossEq :
      ∀ g :
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta,
        loss g =
          realHilbertProjectionSweepPathLoss P sources g := by
    intro g
    exact
      realHilbertProjectionSweep_norm_sq_loss
        P
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2_idempotent
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2_symmetric
          H N hN beta hbeta)
        sources g
  let good :
      Set
        (PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta) :=
    {g | loss (S g) ≤ eta * loss g}
  have hLossContinuous : Continuous loss := by
    dsimp [loss]
    fun_prop
  have hClosed : IsClosed good := by
    exact
      isClosed_le
        (hLossContinuous.comp S.continuous)
        (continuous_const.mul hLossContinuous)
  have hCoreSub :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta ⊆ good := by
    intro g hg
    change loss (S g) ≤ eta * loss g
    rw [hLossEq, hLossEq]
    simpa [P, S, eta] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_pathLoss_le_lossRatio_mul_of_completeOrder
        H N hN s hs beta hbeta hcut sources hNodup hComplete g hg
  have hDense :
      Dense
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore_dense
      H N hN beta hbeta
  have hAll :
      closure
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
            H N hN beta hbeta) ⊆ good :=
    closure_minimal hCoreSub hClosed
  have hfGood : f ∈ good := by
    apply hAll
    rw [hDense.closure_eq]
    exact Set.mem_univ f
  change loss (S f) ≤ eta * loss f at hfGood
  rw [hLossEq, hLossEq] at hfGood
  exact hfGood

end

end MathlibAnalytic
end MGAP4D
