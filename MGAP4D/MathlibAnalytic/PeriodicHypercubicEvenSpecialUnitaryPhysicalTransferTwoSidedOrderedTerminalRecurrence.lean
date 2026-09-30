import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedCyclicForcingBudget
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepStageLocalProfileExactResidual
import MGAP4D.MathlibAnalytic.RealHilbertProjectionSweepTargetResidualForcingBudgetProfileSum
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryHybridPairOneSidedBCF
import Mathlib.Tactic

/-!
# Actual two-sided ordered terminal recurrence

PR #4967 supplies the bounded-core cyclic forcing budget for the genuine
two-sided one-link projection family. This file converts that trajectory
budget into a static profile recurrence and applies the already-proved
two-boundary Schur kernel.

For the canonical sweep through all tagged links, define

* O(source): the residual amplitude at the source's stage of the first sweep;
* T(source): the residual amplitude at the same canonical stage of the second
  sweep, starting from the first sweep terminal vector.

For a target split

  univ.toList = pre ++ target :: suffix,

the between-visits order is suffix ++ pre. Exact sweep geometry gives:

* suffix source residuals = O(source);
* prefix source residuals = T(source).

Hence

  T(target)
    <= sum_source K(target,source) O(source)
       + sum_source K(target,source) T(source),

where K is literally the two-boundary ordered kernel from #4946.

Applying the same Schur bound to the feedback and forcing terms gives

  (1-Q)^2 sum T^2 <= Q^2 sum O^2.

No new coefficient, response symmetry, cardinality factor, or volume factor is
introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section

local instance twoSidedOrderedTerminalRecurrenceSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Complete canonical sweep through all tagged right/left one-link
projections. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkFullSweepVector
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta :=
  realHilbertProjectionSweep
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
      H N hN beta hbeta)
    ((Finset.univ :
      Finset (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H)).toList)
    f

/-- First-sweep local residual amplitude on the tagged two-sided link carrier. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfile
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H → ℝ :=
  realHilbertProjectionSweepStageResidualAmplitude
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
      H N hN beta hbeta)
    ((Finset.univ :
      Finset (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H)).toList)
    f

/-- Second-sweep local residual amplitude, evaluated from the first full-sweep
terminal vector. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkTerminalSweepStageLocalProfile
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H → ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfile
    H N hN beta hbeta
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkFullSweepVector
      H N hN beta hbeta f)

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfile_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (source : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfile
        H N hN beta hbeta f source :=
  realHilbertProjectionSweepStageResidualAmplitude_nonneg
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
      H N hN beta hbeta)
    ((Finset.univ :
      Finset (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H)).toList)
    f source

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkTerminalSweepStageLocalProfile_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (source : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkTerminalSweepStageLocalProfile
        H N hN beta hbeta f source := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfile_nonneg
      H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkFullSweepVector
        H N hN beta hbeta f)
      source

/-- Exact path-loss identity for the first two-sided sweep profile. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfile_sq_sum_eq_pathLoss
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    (∑ source : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfile
        H N hN beta hbeta f source ^ 2) =
      realHilbertProjectionSweepPathLoss
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
          H N hN beta hbeta)
        ((Finset.univ :
          Finset (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H)).toList)
        f := by
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfile] using
    realHilbertProjectionSweepStageResidualAmplitude_sq_sum_eq_pathLoss
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
        H N hN beta hbeta)
      ((Finset.univ :
        Finset (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H)).toList)
      f

/-- Freshness of the distinguished position in the canonical duplicate-free
tagged-link list. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_canonicalSplit_fresh
    (H : ℕ)
    (pre suffix :
      List (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H))
    (target : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H)
    (hSplit :
      (Finset.univ :
        Finset (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H)).toList =
          pre ++ target :: suffix) :
    target ∉ pre := by
  have hNodup : (pre ++ target :: suffix).Nodup := by
    rw [← hSplit]
    exact Finset.nodup_toList _
  have hMiddle : (target :: (pre ++ suffix)).Nodup :=
    List.nodup_middle.mp hNodup
  have hNot : target ∉ pre ++ suffix :=
    hMiddle.notMem
  intro ht
  exact hNot (by simp [ht])

/-- At a displayed canonical position, the first-sweep profile is exactly the
norm of the actual one-link residual at that prefix stage. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfile_eq_stageResidual_norm_of_canonicalPrefix
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (pre suffix :
      List (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H))
    (source : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hSplit :
      (Finset.univ :
        Finset (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H)).toList =
          pre ++ source :: suffix) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfile
        H N hN beta hbeta f source =
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
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_canonicalSplit_fresh
      H pre suffix source hSplit
  have hNodup : (pre ++ source :: suffix).Nodup := by
    rw [← hSplit]
    exact Finset.nodup_toList _
  have hTailNodup : (source :: suffix).Nodup :=
    hNodup.of_append_right
  have hSuffix : source ∉ suffix :=
    (List.nodup_cons.mp hTailNodup).1
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfile
  rw [hSplit]
  exact
    realHilbertProjectionSweepStageResidualAmplitude_append_cons_eq_norm
      P pre suffix f source hFresh hSuffix

/-- Main pointwise two-sided terminal recurrence with the literal ordered block
kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_terminalProfile_le_ordered_forcing_feedback
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
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hf :
      f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta)
    (target : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkTerminalSweepStageLocalProfile
        H N hN beta hbeta f target ≤
      (∑ source : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H,
        GroundStateSourceFixedPairEnergy.twoBoundaryOrderedKernel
            H N hN beta hbeta s target source *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfile
            H N hN beta hbeta f source) +
        ∑ source : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H,
          GroundStateSourceFixedPairEnergy.twoBoundaryOrderedKernel
              H N hN beta hbeta s target source *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkTerminalSweepStageLocalProfile
              H N hN beta hbeta f source := by
  classical
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
      H N hN beta hbeta
  let K :=
    GroundStateSourceFixedPairEnergy.twoBoundaryOrderedKernel
      H N hN beta hbeta s
  let O :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfile
      H N hN beta hbeta f
  let T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkTerminalSweepStageLocalProfile
      H N hN beta hbeta f
  let Full :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkFullSweepVector
      H N hN beta hbeta f
  have hMem :
      target ∈
        (Finset.univ :
          Finset (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H)).toList := by
    simp
  obtain ⟨pre, suffix, hSplit⟩ :=
    List.mem_iff_append.mp hMem
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
    unfold Full
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkFullSweepVector
    change
      realHilbertProjectionSweep P
          ((Finset.univ :
            Finset (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H)).toList) f =
        realHilbertProjectionSweep P suffix x0
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
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfile_eq_stageResidual_norm_of_canonicalPrefix
        H N hN beta hbeta pre suffix target Full hSplit
    change
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfile
          H N hN beta hbeta Full target =
        ‖realHilbertProjectionSweep P (suffix ++ pre) x0 -
          P target (realHilbertProjectionSweep P (suffix ++ pre) x0)‖
    rw [hProfile, hTerminalStage]
  have hNodup : (pre ++ target :: suffix).Nodup := by
    rw [← hSplit]
    exact Finset.nodup_toList _
  have hPreNodup : pre.Nodup :=
    hNodup.of_append_left
  have hTailNodup : (target :: suffix).Nodup :=
    hNodup.of_append_right
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
        (Finset.univ :
          Finset (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H)).toList =
          (pre ++ target :: before) ++ source :: after := by
      rw [hSplit, hSuffixSplit]
      simp [List.append_assoc]
    have hProfile :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfile_eq_stageResidual_norm_of_canonicalPrefix
        H N hN beta hbeta
        (pre ++ target :: before) after source f hSourceSplit
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
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfile
          H N hN beta hbeta f source
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
        (Finset.univ :
          Finset (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H)).toList =
          before ++ source :: (after ++ target :: suffix) := by
      rw [hSplit, hPreSplit]
      simp [List.append_assoc]
    have hProfile :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfile_eq_stageResidual_norm_of_canonicalPrefix
        H N hN beta hbeta
        before (after ++ target :: suffix) source Full hSourceSplit
    have hNorm :
        ‖realHilbertProjectionSweep P before
              (realHilbertProjectionSweep P suffix x0) -
            P source
              (realHilbertProjectionSweep P before
                (realHilbertProjectionSweep P suffix x0))‖ =
          T source := by
      change _ =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfile
          H N hN beta hbeta Full source
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
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfile_nonneg
            H N hN beta hbeta f source))
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
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkTerminalSweepStageLocalProfile_nonneg
            H N hN beta hbeta f source))
  exact hRestricted.trans (_root_.add_le_add hSuffixLe hPreLe)

/-- Apply the already-closed two-boundary Schur estimate to both the forcing
and feedback terms of the actual terminal recurrence. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_terminalProfile_energy_le_orderedSchur_feedback
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
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkTerminalSweepStageLocalProfile
            H N hN beta hbeta f target ^ 2 ≤
      GroundStateSourceFixedPairEnergy.twoBoundaryOrderedSchurCoefficient
          s beta ^ 2 *
        ∑ source : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfile
            H N hN beta hbeta f source ^ 2 := by
  let matrix :=
    GroundStateSourceFixedPairEnergy.twoBoundaryOrderedKernel
      H N hN beta hbeta s
  let terminal :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkTerminalSweepStageLocalProfile
      H N hN beta hbeta f
  let original :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfile
      H N hN beta hbeta f
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
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkTerminalSweepStageLocalProfile_nonneg
        H N hN beta hbeta f target
  have hOriginal :
      ∀ source, 0 ≤ original source := by
    intro source
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfile_nonneg
        H N hN beta hbeta f source
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
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_terminalProfile_le_ordered_forcing_feedback
        H N hN beta hbeta s (by linarith) hStrict hBetaLt f hf target
  have hCoercive :=
    FiniteSchurOneSidedProfile.global_energy_coercive
      matrix Q hQ.1 hQ.2 hMatrix hSchur
      terminal forced hTerminal hForced hRecurrence
  have hForceBound := hSchur original
  exact hCoercive.trans hForceBound

end

end MathlibAnalytic
end MGAP4D
