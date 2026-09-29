import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOrderedAllLinkSweepResidual
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedOrderedLossContraction
import MGAP4D.MathlibAnalytic.RealHilbertProjectionSweepInitialResidualControl

/-!
# Geometric path loss for complete mixed-color right-link sweeps

The actual source profile satisfies a <= initialResidual + k^T a. Apply the
existing one-sided Schur theorem to obtain (1-Q)^2 pathLoss <= initialEnergy.
Combine with #4941's terminalEnergy <= Q^2 pathLoss, obtaining loss decay
with EXACTLY eta=(Q/(1-Q))^2. Every input is an arbitrary joint-L2 vector.
-/

namespace MGAP4D.MathlibAnalytic
open scoped BigOperators
noncomputable section

attribute [local instance]
  groundStateJointOneLinkBoundedCoreSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkBoundedCoreSpecialUnitaryCompactSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkBoundedCoreSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitaryBorelSpace
  groundStateJointOneLinkBoundedCoreSpatialLinkFintype

namespace GroundStateSourceFixedPairEnergy
variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "JL2" => PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta
local notation "P" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2 H N hN beta hbeta
local notation "k" => jointLeakageNormCoefficient H N hN beta hbeta

/-- Initial residuals control exact path loss without a source-count factor.
Completeness is not required here, only absence of duplicate visits. -/
theorem allLinkSweep_pathLoss_controlled_by_initialResidual
    (s : ℝ) (hs : 8 < s) (hcut : beta ≤ jointLeakageSchurCutoff s hs)
    (sources : List Link) (hNodup : sources.Nodup) (f : JL2) :
    (1 - jointLeakageSchurCoefficient s beta) ^ 2 * realHilbertProjectionSweepPathLoss P sources f ≤
      ∑ e : Link, ‖f - P e f‖ ^ 2 := by
  classical
  let matrix : Link → Link → ℝ := fun target source => k s source target
  let profile := realHilbertProjectionSweepSourceResidualProfile P sources f
  let initial : Link → ℝ := fun e => ‖f - P e f‖
  have hQ := jointLeakageSchurCoefficient_nonneg_lt_one s hs beta hbeta hcut
  have hStrict := hcut.trans (jointLeakageSchurCutoff_le_strictPhysicalSweepCutoff s hs)
  have hStep : ∀ source target (x : JL2),
      ‖P source x - P target (P source x)‖ ≤
        ‖x - P target x‖ + k s source target * ‖x - P source x‖ :=
    fun source target x => sourceUpdate_targetResidual_norm_le_add_sourceResidual_allL2
      H N hN beta hbeta s (by linarith) hStrict source target x
  have hOneSided : ∀ target, profile target ≤
      initial target + ∑ source, matrix target source * profile source := by
    intro target
    have h := realHilbertProjectionSweepSourceResidualProfile_le_budget_add_initial
      P (k s) (fun source target => jointLeakageNormCoefficient_nonneg H N hN beta hbeta s source target)
      hStep sources f hNodup target
    rw [realHilbertProjectionSweepTargetResidualForcingBudget_eq_weightedSourceProfile] at h
    exact h.trans_eq (add_comm _ _)
  have hSchur : ∀ v : Link → ℝ,
      (∑ target, (∑ source, matrix target source * v source) ^ 2) ≤
        jointLeakageSchurCoefficient s beta ^ 2 * ∑ source, v source ^ 2 :=
    fun v => jointLeakageNormCoefficient_transpose_action_sq_sum_le H N hN s hs beta hbeta
      (hcut.trans (jointLeakageSchurCutoff_le_shellCutoff s hs)) v
  have hEnergy := FiniteSchurOneSidedProfile.global_energy_coercive
    matrix (jointLeakageSchurCoefficient s beta) hQ.1 hQ.2
    (fun target source => jointLeakageNormCoefficient_nonneg H N hN beta hbeta s source target)
    hSchur profile initial
    (fun e => realHilbertProjectionSweepSourceResidualProfile_nonneg P sources f e)
    (fun e => norm_nonneg _) hOneSided
  have hProfile : (∑ e : Link, profile e ^ 2) = realHilbertProjectionSweepPathLoss P sources f :=
    realHilbertProjectionSweepSourceResidualProfile_sq_sum_eq_pathLoss P sources f hNodup
  rw [hProfile] at hEnergy
  exact hEnergy

/-- The next complete sweep loses at most eta times the current loss. No core
premise, new cutoff, or restriction to one color is introduced. -/
theorem allLinkSweep_pathLoss_le_lossRatio_mul
    (s : ℝ) (hs : 8 < s) (hcut : beta ≤ jointLeakageLossContractionCutoff s hs)
    (sources : List Link) (hNodup : sources.Nodup) (hComplete : ∀ e, e ∈ sources)
    (f : JL2) :
    realHilbertProjectionSweepPathLoss P sources (realHilbertProjectionSweep P sources f) ≤
      jointLeakageLossRatio s beta * realHilbertProjectionSweepPathLoss P sources f := by
  have hSchurCut := hcut.trans (jointLeakageLossContractionCutoff_le_schurCutoff s hs)
  have hQ := jointLeakageSchurCoefficient_nonneg_lt_half s hs beta hbeta hcut
  have hDen : 0 < (1 - jointLeakageSchurCoefficient s beta) ^ 2 :=
    sq_pos_of_pos (by linarith [hQ.2])
  have hInitial := allLinkSweep_pathLoss_controlled_by_initialResidual
    H N hN beta hbeta s hs hSchurCut sources hNodup (realHilbertProjectionSweep P sources f)
  have hTerminal := allLinkSweep_terminalResidual_sq_sum_le_schurCoefficient_sq_mul_pathLoss
    H N hN s hs beta hbeta hSchurCut sources hNodup hComplete f
  have hEnergy := hInitial.trans hTerminal
  calc
    _ ≤ (jointLeakageSchurCoefficient s beta ^ 2 * realHilbertProjectionSweepPathLoss P sources f) /
        (1 - jointLeakageSchurCoefficient s beta) ^ 2 :=
      (le_div_iff₀ hDen).2 (by simpa only [mul_comm] using hEnergy)
    _ = _ := by rw [jointLeakageLossRatio, div_pow]; ring

/-- Geometric decay along the SAME arbitrary-order complete right-link sweep. -/
theorem allLinkSweep_iteratedPathLoss_le_geometric
    (s : ℝ) (hs : 8 < s) (hcut : beta ≤ jointLeakageLossContractionCutoff s hs)
    (sources : List Link) (hNodup : sources.Nodup) (hComplete : ∀ e, e ∈ sources)
    (f : JL2) (n : ℕ) :
    realHilbertProjectionSweepPathLoss P sources
        ((realHilbertProjectionSweep P sources : JL2 → JL2)^[n] f) ≤
      jointLeakageLossRatio s beta ^ n * realHilbertProjectionSweepPathLoss P sources f := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      calc
        _ ≤ jointLeakageLossRatio s beta ^ n *
            realHilbertProjectionSweepPathLoss P sources (realHilbertProjectionSweep P sources f) :=
          ih (realHilbertProjectionSweep P sources f)
        _ ≤ jointLeakageLossRatio s beta ^ n *
            (jointLeakageLossRatio s beta * realHilbertProjectionSweepPathLoss P sources f) :=
          mul_le_mul_of_nonneg_left
            (allLinkSweep_pathLoss_le_lossRatio_mul H N hN beta hbeta s hs hcut sources hNodup hComplete f)
            (pow_nonneg (jointLeakageLossRatio_nonneg s beta) n)
        _ = _ := by rw [pow_succ]; ring

end GroundStateSourceFixedPairEnergy
end
end MGAP4D.MathlibAnalytic
