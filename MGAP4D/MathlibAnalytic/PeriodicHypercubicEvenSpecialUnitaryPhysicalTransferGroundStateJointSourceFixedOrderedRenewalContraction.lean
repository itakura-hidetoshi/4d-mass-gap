import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedOrderedLossContraction
import MGAP4D.MathlibAnalytic.RealHilbertProjectionSweepGeometricConvergence

/-!
# Actual zero-tail and strict renewal contraction for fixed-color sweeps

The geometric path-loss theorem from #4938 supplies the actual orbit input to
the generic convergence theorem. The full-space common-fixed geometry and
absorption identify its limit with the genuine color block, even though the
limit need not be a bounded-core vector. The physical defect tail is therefore
zero, not an additional hypothesis.

Apply the existing renewal-tail comparison to get
  D_c(S_c f) <= eta(s,beta) D_c(f),  0 <= eta < 1,
and average these actual fixed-color inequalities with the unchanged 1/6.
The auxiliary finite-list constant used to prove convergence is absent from
these uniform estimates. No cross-link commutativity, old physical envelope,
density extension, positive-beta transfer gap or continuum claim is made.
-/

namespace MGAP4D.MathlibAnalytic

open Filter
open scoped Topology BigOperators

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

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "CLink" => PeriodicHypercubicEvenFixedSpatialColorLink H
local notation "JL2" => PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta
local notation "Core" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore H N hN beta hbeta
local notation "P" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2 H N hN beta hbeta
local notation "S" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector H N hN beta hbeta
local notation "B" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2 H N hN beta hbeta
local notation "L" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss H N hN beta hbeta
local notation "DV" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector H N hN beta hbeta
local notation "Dmean" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepBlockDefectMeanNormSq H N hN beta hbeta
local notation "Dnext" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkNextSweepBlockDefectMeanNormSq H N hN beta hbeta
local notation "Lterm" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepPathLoss H N hN beta hbeta

private theorem fixedColor_iterates_mem_core
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (f : JL2) (hf : f ∈ Core) (n : ℕ) : (S color)^[n] f ∈ Core := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweep_mem_boundedConcreteCore
        H N hN beta hbeta color ((Finset.univ : Finset (CLink color)).toList)
        ((S color)^[n] f) ih

/-- The actual bounded-core orbit converges to the genuine color projection.
No quantitative projection-convergence rate or physical zero-tail is assumed. -/
theorem fixedColor_iterates_tendsto_colorProjection
    (s : ℝ) (hs : 8 < s) (hcut : beta ≤ jointLeakageLossContractionCutoff s hs)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor) (f : JL2) (hf : f ∈ Core) :
    Tendsto (fun n : ℕ => (S color)^[n] f) atTop (𝓝 (B color f)) := by
  let cs := (Finset.univ : Finset (CLink color)).toList
  have hEta := jointLeakageLossRatio_nonneg_lt_one s hs beta hbeta hcut
  exact realHilbertProjectionSweep_tendsto_block_of_geometric_pathLoss
    (P color) cs (B color) (jointLeakageLossRatio s beta) hEta.1 hEta.2
    (fun g => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2_fullOneLinkSweep_eq
      H N hN beta hbeta color g)
    (fun g hg =>
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweep_fixed_iff_color_fixed
        H N hN beta hbeta color g).mp hg)
    f (fun n => fixedColor_iteratedPathLoss_le_geometric H N hN beta hbeta s hs hcut color f hf n)

/-- The physical defect tail vanishes on the actual orbit. Absorption is used
at every finite stage; no pointwise representative or core membership of the
limit is required. -/
theorem fixedColor_defect_iterates_tendsto_zero
    (s : ℝ) (hs : 8 < s) (hcut : beta ≤ jointLeakageLossContractionCutoff s hs)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor) (f : JL2) (hf : f ∈ Core) :
    Tendsto (fun n : ℕ => ‖DV color ((S color)^[n] f)‖ ^ 2) atTop (𝓝 0) := by
  have hLimit := fixedColor_iterates_tendsto_colorProjection H N hN beta hbeta s hs hcut color f hf
  have hShift : Tendsto (fun n : ℕ => (S color)^[n + 1] f) atTop (𝓝 (B color f)) :=
    (tendsto_add_atTop_iff_nat 1).2 hLimit
  have hBIter : ∀ n : ℕ, B color ((S color)^[n] f) = B color f := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2_fullOneLinkSweep_eq
          H N hN beta hbeta color ((S color)^[n] f)).trans ih
  have hDiff : Tendsto (fun n : ℕ => (S color)^[n + 1] f - B color f)
      atTop (𝓝 (B color f - B color f)) := hShift.sub tendsto_const_nhds
  have hZero : Tendsto (fun n : ℕ => ‖(S color)^[n + 1] f - B color f‖ ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hDiff.norm.pow 2
  change Tendsto (fun n : ℕ =>
    ‖S color ((S color)^[n] f) - B color ((S color)^[n] f)‖ ^ 2) atTop (𝓝 0)
  simpa only [Function.iterate_succ_apply', hBIter] using hZero

/-- Strict physical renewal contraction with EXACTLY the existing eta. The
vanishing-tail premise of #4938 is discharged, not exposed as a new input. -/
theorem fixedColor_nextDefect_le_lossRatio_mul
    (s : ℝ) (hs : 8 < s) (hcut : beta ≤ jointLeakageLossContractionCutoff s hs)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor) (f : JL2) (hf : f ∈ Core) :
    ‖DV color (S color f)‖ ^ 2 ≤ jointLeakageLossRatio s beta * ‖DV color f‖ ^ 2 := by
  let defects : ℕ → ℝ := fun n => ‖DV color ((S color)^[n] f)‖ ^ 2
  let losses : ℕ → ℝ := fun n => L color ((S color)^[n] f)
  have hRenew : ∀ n, defects n = losses (n + 1) + defects (n + 1) := by
    intro n
    simpa only [defects, losses, Function.iterate_succ_apply'] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefect_norm_sq_eq_terminalSweepPathLoss_add_nextDefect_norm_sq
        H N hN beta hbeta color ((S color)^[n] f)
  have hLoss : ∀ n, losses (n + 2) ≤ jointLeakageLossRatio s beta * losses (n + 1) := by
    intro n
    change L color ((S color)^[n + 1 + 1] f) ≤
      jointLeakageLossRatio s beta * L color ((S color)^[n + 1] f)
    rw [Function.iterate_succ_apply']
    exact fixedColor_terminalPathLoss_le_lossRatio_mul H N hN beta hbeta s hs hcut color
      ((S color)^[n + 1] f) (fixedColor_iterates_mem_core H N hN beta hbeta color f hf (n + 1))
  have hTail : Tendsto defects atTop (𝓝 0) :=
    fixedColor_defect_iterates_tendsto_zero H N hN beta hbeta s hs hcut color f hf
  have h := RenewalTail.defect_succ_le_mul_of_tendsto_zero
    defects losses (jointLeakageLossRatio s beta) hRenew hLoss hTail
  simpa [defects] using h

/-- The same volume/rank-independent ratio controls the actual next defect
mean. Each term repeats its OWN fixed-color sweep; no averaged sweep is invented. -/
theorem sixSpatial_nextDefectMean_le_lossRatio_mul
    (s : ℝ) (hs : 8 < s) (hcut : beta ≤ jointLeakageLossContractionCutoff s hs)
    (f : JL2) (hf : f ∈ Core) : Dnext f ≤ jointLeakageLossRatio s beta * Dmean f := by
  have hSum :
      (∑ c : Fin 6, ‖DV (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)
        (S (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f)‖ ^ 2) ≤
      ∑ c : Fin 6, jointLeakageLossRatio s beta *
        ‖DV (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f‖ ^ 2 :=
    Finset.sum_le_sum fun c _ => fixedColor_nextDefect_le_lossRatio_mul
      H N hN beta hbeta s hs hcut (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f hf
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkNextSweepBlockDefectMeanNormSq
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepBlockDefectMeanNormSq
  calc
    _ ≤ (1 / 6 : ℝ) * ∑ c : Fin 6, jointLeakageLossRatio s beta *
        ‖DV (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hSum (by norm_num)
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- The actual positive renewal margin, using the exact six-color identity. -/
theorem sixSpatial_terminalPathLoss_ge_one_sub_lossRatio_mul_defectMean
    (s : ℝ) (hs : 8 < s) (hcut : beta ≤ jointLeakageLossContractionCutoff s hs)
    (f : JL2) (hf : f ∈ Core) :
    (1 - jointLeakageLossRatio s beta) * Dmean f ≤ Lterm f := by
  have hNext := sixSpatial_nextDefectMean_le_lossRatio_mul H N hN beta hbeta s hs hcut f hf
  have hRenew := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepBlockDefectMeanNormSq_eq_terminalSweepPathLoss_add_nextDefectMeanNormSq
    H N hN beta hbeta f
  nlinarith

end GroundStateSourceFixedPairEnergy
end
end MGAP4D.MathlibAnalytic
