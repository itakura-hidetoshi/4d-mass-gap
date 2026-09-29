import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedOrderedSchurEnvelope
import MGAP4D.MathlibAnalytic.RealHilbertProjectionSweepSourceResidualProfile

/-!
# Ordered all-right-link sweeps on the full genuine joint L2 carrier

The source-fixed analytic estimate already applies to every pair of distinct
right links, not only links in one color. Extend its continuous one-step norm
inequality from the existing dense core to all joint L2. Diagonal updates have
zero target residual by idempotence and need no analytic hypothesis.

For any complete duplicate-free list of right links, in its actual order,
  sum_target ||S f - P_target(S f)||^2 <= Q^2 * pathLoss(S,f).
The occurrence-summed source profile identifies the exact forcing energy;
the SAME k(source,target) and Q from #4936 supply Schur control, with no
cardinality or color-count factor. No projection order is changed.

All updates still retain the other boundary. This is NOT a physical-sector
Poincare theorem or a positive-beta transfer-gap claim. No beta-zero 5/6
coefficient, common-fixed-to-constants assertion, or cross-boundary estimate
is assumed.
-/

namespace MGAP4D.MathlibAnalytic

open Set
open scoped BigOperators

noncomputable section

attribute [local instance]
  groundStateJointOneLinkBoundedCoreSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkBoundedCoreSpecialUnitaryCompactSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkBoundedCoreSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitaryBorelSpace
  groundStateJointOneLinkBoundedCoreSpatialLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkUnique

namespace GroundStateSourceFixedPairEnergy

section FixedParameters

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "JL2" => PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta
local notation "Core" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore H N hN beta hbeta
local notation "P" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2 H N hN beta hbeta
local notation "k" => jointLeakageNormCoefficient H N hN beta hbeta
local notation "strictCutoff" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff

/-- Extend the existing off-diagonal analytic norm inequality by continuity
and density, then handle the diagonal exactly. No core premise remains. -/
theorem sourceUpdate_targetResidual_norm_le_add_sourceResidual_allL2
    (s : ℝ) (hs : 1 < s) (hcut : beta ≤ strictCutoff s)
    (source target : Link) (f : JL2) :
    ‖P source f - P target (P source f)‖ ≤
      ‖f - P target f‖ + k s source target * ‖f - P source f‖ := by
  by_cases hEq : target = source
  · subst target
    have hIdem : P source (P source f) = P source f := by
      simpa only [ContinuousLinearMap.comp_apply] using congrArg
        (fun A : JL2 →L[ℝ] JL2 => A f)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_idempotent
          H N hN beta hbeta source)
    rw [hIdem, sub_self, norm_zero]
    exact add_nonneg (norm_nonneg _) (mul_nonneg
      (jointLeakageNormCoefficient_nonneg H N hN beta hbeta s source source) (norm_nonneg _))
  · let good : Set JL2 := {g | ‖P source g - P target (P source g)‖ ≤
      ‖g - P target g‖ + k s source target * ‖g - P source g‖}
    have hLeft : Continuous (fun g : JL2 => ‖P source g - P target (P source g)‖) := by fun_prop
    have hRight : Continuous (fun g : JL2 =>
        ‖g - P target g‖ + k s source target * ‖g - P source g‖) := by fun_prop
    have hClosed : IsClosed good := isClosed_le hLeft hRight
    have hCoreSub : Core ⊆ good := by
      intro g hg
      exact sourceUpdate_targetResidual_norm_le_add_sourceResidual
        H N hN beta hbeta s hs hcut source g hg target hEq
    have hClosureSub : closure Core ⊆ good := closure_minimal hCoreSub hClosed
    have hDense : Dense Core :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore_dense
        H N hN beta hbeta
    exact hClosureSub (by rw [hDense.closure_eq]; exact Set.mem_univ f)

/-- The existing budget on arbitrary right-link lists, with its actual stages. -/
def allLinkSweepOrderedResidualBudget
    (s : ℝ) (sources : List Link) (f : JL2) (target : Link) : ℝ :=
  realHilbertProjectionSweepTargetResidualForcingBudget P
    (fun source x => k s source target * ‖x - P source x‖) sources f

/-- The ordered budget is nonnegative even for lists containing repetitions. -/
theorem allLinkSweepOrderedResidualBudget_nonneg
    (s : ℝ) (sources : List Link) (f : JL2) (target : Link) :
    0 ≤ allLinkSweepOrderedResidualBudget H N hN beta hbeta s sources f target := by
  classical
  unfold allLinkSweepOrderedResidualBudget
  rw [realHilbertProjectionSweepTargetResidualForcingBudget_eq_weightedSourceProfile]
  exact Finset.sum_nonneg fun source _ => mul_nonneg
    (jointLeakageNormCoefficient_nonneg H N hN beta hbeta s source target)
    (realHilbertProjectionSweepSourceResidualProfile_nonneg P sources f source)

/-- Actual mixed-color trajectory propagation on ALL joint L2. The universal
receiver is now legitimate because its analytic premise was extended first. -/
theorem allLinkSweep_targetResidual_le_orderedBudget_add_initial
    (s : ℝ) (hs : 1 < s) (hcut : beta ≤ strictCutoff s)
    (sources : List Link) (f : JL2) (target : Link) :
    ‖realHilbertProjectionSweep P sources f - P target (realHilbertProjectionSweep P sources f)‖ ≤
      allLinkSweepOrderedResidualBudget H N hN beta hbeta s sources f target + ‖f - P target f‖ := by
  apply realHilbertProjectionSweep_targetResidual_norm_le_forcingBudget_add_initial
    P target (fun source x => k s source target * ‖x - P source x‖)
  intro source x
  simpa only [add_comm] using sourceUpdate_targetResidual_norm_le_add_sourceResidual_allL2
    H N hN beta hbeta s hs hcut source target x

/-- Once the target has been visited, its initial residual is zero. All
forcing before that visit may then be added only because it is nonnegative. -/
theorem allLinkSweep_targetResidual_le_orderedBudget_of_mem
    (s : ℝ) (hs : 1 < s) (hcut : beta ≤ strictCutoff s)
    (sources : List Link) (f : JL2) (target : Link) (hMem : target ∈ sources) :
    ‖realHilbertProjectionSweep P sources f - P target (realHilbertProjectionSweep P sources f)‖ ≤
      allLinkSweepOrderedResidualBudget H N hN beta hbeta s sources f target := by
  obtain ⟨pre, suffix, hSplit⟩ := List.mem_iff_append.mp hMem
  let x0 := P target (realHilbertProjectionSweep P pre f)
  have hFixed : P target x0 = x0 := by
    simpa only [x0, ContinuousLinearMap.comp_apply] using congrArg
      (fun A : JL2 →L[ℝ] JL2 => A (realHilbertProjectionSweep P pre f))
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_idempotent
        H N hN beta hbeta target)
  have hSuffix := allLinkSweep_targetResidual_le_orderedBudget_add_initial
    H N hN beta hbeta s hs hcut suffix x0 target
  simp only [hFixed, sub_self, norm_zero, add_zero] at hSuffix
  have hFull : realHilbertProjectionSweep P sources f =
      realHilbertProjectionSweep P suffix x0 := by
    rw [hSplit, realHilbertProjectionSweep_append P pre (target :: suffix) f] <;> rfl
  have hBudget : allLinkSweepOrderedResidualBudget H N hN beta hbeta s suffix x0 target ≤
      allLinkSweepOrderedResidualBudget H N hN beta hbeta s sources f target := by
    change realHilbertProjectionSweepTargetResidualForcingBudget P
        (fun source x => k s source target * ‖x - P source x‖) suffix x0 ≤
      realHilbertProjectionSweepTargetResidualForcingBudget P
        (fun source x => k s source target * ‖x - P source x‖) sources f
    rw [hSplit, realHilbertProjectionSweepTargetResidualForcingBudget_append]
    change allLinkSweepOrderedResidualBudget H N hN beta hbeta s suffix x0 target ≤
      allLinkSweepOrderedResidualBudget H N hN beta hbeta s pre f target +
        (k s target target * ‖realHilbertProjectionSweep P pre f -
          P target (realHilbertProjectionSweep P pre f)‖ +
          allLinkSweepOrderedResidualBudget H N hN beta hbeta s suffix x0 target)
    have hPre := allLinkSweepOrderedResidualBudget_nonneg H N hN beta hbeta s pre f target
    have hTarget : 0 ≤ k s target target * ‖realHilbertProjectionSweep P pre f -
        P target (realHilbertProjectionSweep P pre f)‖ := mul_nonneg
      (jointLeakageNormCoefficient_nonneg H N hN beta hbeta s target target) (norm_nonneg _)
    linarith
  rw [hFull]
  exact hSuffix.trans hBudget

end FixedParameters

/-- The SAME ordered Schur kernel acts on the single actual source profile.
Nodup is exactly the condition needed to identify its energy with path loss. -/
theorem allLinkSweep_orderedBudget_sq_sum_le_schurCoefficient_sq_mul_pathLoss
    (H N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta) (hcut : beta ≤ jointLeakageSchurCutoff s hs)
    (sources : List (PeriodicHypercubicEvenSpatialSliceLink H)) (hNodup : sources.Nodup)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      allLinkSweepOrderedResidualBudget H N hN beta hbeta s sources f target ^ 2) ≤
      jointLeakageSchurCoefficient s beta ^ 2 *
        realHilbertProjectionSweepPathLoss
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN beta hbeta) sources f := by
  classical
  let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
    H N hN beta hbeta
  let profile := realHilbertProjectionSweepSourceResidualProfile P sources f
  have hSchur := jointLeakageNormCoefficient_transpose_action_sq_sum_le
    H N hN s hs beta hbeta (hcut.trans (jointLeakageSchurCutoff_le_shellCutoff s hs)) profile
  calc
    _ = ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          jointLeakageNormCoefficient H N hN beta hbeta s source target * profile source) ^ 2 := by
      apply Finset.sum_congr rfl
      intro target _
      rw [allLinkSweepOrderedResidualBudget,
        realHilbertProjectionSweepTargetResidualForcingBudget_eq_weightedSourceProfile]
    _ ≤ jointLeakageSchurCoefficient s beta ^ 2 * ∑ source, profile source ^ 2 := hSchur
    _ = _ := by
      dsimp [profile]
      rw [realHilbertProjectionSweepSourceResidualProfile_sq_sum_eq_pathLoss P sources f hNodup]

/-- Final residual energy after ANY complete duplicate-free right-link sweep.
All colors may occur. The argument is arbitrary genuine joint L2, and the
coefficient is Q squared with no normalization/cardinality loss. -/
theorem allLinkSweep_terminalResidual_sq_sum_le_schurCoefficient_sq_mul_pathLoss
    (H N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta) (hcut : beta ≤ jointLeakageSchurCutoff s hs)
    (sources : List (PeriodicHypercubicEvenSpatialSliceLink H))
    (hNodup : sources.Nodup) (hComplete : ∀ target, target ∈ sources)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta) :
    let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2 H N hN beta hbeta
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      ‖realHilbertProjectionSweep P sources f - P target (realHilbertProjectionSweep P sources f)‖ ^ 2) ≤
      jointLeakageSchurCoefficient s beta ^ 2 * realHilbertProjectionSweepPathLoss P sources f := by
  let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
    H N hN beta hbeta
  have hStrict := hcut.trans (jointLeakageSchurCutoff_le_strictPhysicalSweepCutoff s hs)
  have hEach : ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
      ‖realHilbertProjectionSweep P sources f - P target (realHilbertProjectionSweep P sources f)‖ ^ 2 ≤
        allLinkSweepOrderedResidualBudget H N hN beta hbeta s sources f target ^ 2 := by
    intro target
    exact (sq_le_sq₀ (norm_nonneg _)
      (allLinkSweepOrderedResidualBudget_nonneg H N hN beta hbeta s sources f target)).2
      (allLinkSweep_targetResidual_le_orderedBudget_of_mem
        H N hN beta hbeta s (by linarith) hStrict sources f target (hComplete target))
  exact (Finset.sum_le_sum (fun target _ => hEach target)).trans
    (allLinkSweep_orderedBudget_sq_sum_le_schurCoefficient_sq_mul_pathLoss
      H N hN s hs beta hbeta hcut sources hNodup f)

end GroundStateSourceFixedPairEnergy
end
end MGAP4D.MathlibAnalytic
