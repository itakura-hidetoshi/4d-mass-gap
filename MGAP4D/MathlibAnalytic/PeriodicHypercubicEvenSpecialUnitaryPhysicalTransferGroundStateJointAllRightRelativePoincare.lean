import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOrderedAllLinkLossContraction
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointAllRightRetainedGeometry
import MGAP4D.MathlibAnalytic.RealHilbertProjectionSweepGeometricConvergence

/-!
# Uniform all-right-link Poincare relative to the retained left boundary

All complete mixed-color right-link sweeps converge to literal conditional
expectation onto the full left boundary. Combine exact norm-loss renewal,
proved zero tails, and the initial-profile Schur bound to obtain
  (1-2Q) ||f-E[f|left]||^2 <= sum_e ||f-P_e f||^2.
No list length survives in this inequality. The energy on the right is the
UNNORMALIZED all-right-link energy, not the six-color average. No physical
sector, two-sided Poincare, or positive-beta transfer gap is asserted.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory Filter
open scoped BigOperators Topology InnerProductSpace InnerProduct
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
local notation "Cleft" => allRightLeftRetainedCondExpL2 H N hN beta hbeta

/-- An arbitrary-order complete right-link sweep has the actual left-retained
conditional expectation as its limit. Every joint-L2 input is allowed. -/
theorem allLinkSweep_iterates_tendsto_leftRetained
    (s : ℝ) (hs : 8 < s) (hcut : beta ≤ jointLeakageLossContractionCutoff s hs)
    (sources : List Link) (hNodup : sources.Nodup) (hComplete : ∀ e, e ∈ sources)
    (f : JL2) :
    Tendsto (fun n : ℕ => (realHilbertProjectionSweep P sources : JL2 → JL2)^[n] f)
      atTop (𝓝 (Cleft f)) := by
  have hEta := jointLeakageLossRatio_nonneg_lt_one s hs beta hbeta hcut
  have hFixed : ∀ g : JL2, realHilbertProjectionSweep P sources g = g → Cleft g = g := by
    intro g hg
    have hEach := (realHilbertProjectionSweep_apply_eq_self_iff_forall_mem_fixed P
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_idempotent H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_symmetric H N hN beta hbeta)
      sources g).mp hg
    exact (allRightLink_fixed_iff_leftRetained H N hN beta hbeta g).mp
      (fun e => hEach e (hComplete e))
  exact realHilbertProjectionSweep_tendsto_block_of_geometric_pathLoss
    P sources Cleft (jointLeakageLossRatio s beta) hEta.1 hEta.2
    (fun g => allRightLeftRetained_absorb_sweep H N hN beta hbeta sources g) hFixed f
    (fun n => allLinkSweep_iteratedPathLoss_le_geometric H N hN beta hbeta s hs hcut sources hNodup hComplete f n)

/-- Exact relative norm-loss identity; no high-temperature assumption or
completeness of the source list is needed for this equality. -/
theorem allLinkSweep_leftRetained_pythagoras (sources : List Link) (f : JL2) :
    ‖f - Cleft f‖ ^ 2 = realHilbertProjectionSweepPathLoss P sources f +
      ‖realHilbertProjectionSweep P sources f - Cleft (realHilbertProjectionSweep P sources f)‖ ^ 2 := by
  have hFirst := realHilbertProjection_residual_norm_sq Cleft
    (allRightLeftRetained_idempotent H N hN beta hbeta)
    (allRightLeftRetained_symmetric H N hN beta hbeta) f
  have hSecond := realHilbertProjection_residual_norm_sq Cleft
    (allRightLeftRetained_idempotent H N hN beta hbeta)
    (allRightLeftRetained_symmetric H N hN beta hbeta) (realHilbertProjectionSweep P sources f)
  rw [allRightLeftRetained_absorb_sweep H N hN beta hbeta sources f] at hSecond
  have hLoss := realHilbertProjectionSweep_norm_sq_loss P
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_idempotent H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_symmetric H N hN beta hbeta)
    sources f
  rw [allRightLeftRetained_absorb_sweep H N hN beta hbeta sources f]
  nlinarith

/-- Loss controls the entire LEFT-CENTERED variance with no list-length loss.
The tail is discharged by the preceding actual convergence theorem. -/
theorem allLinkSweep_pathLoss_ge_one_sub_lossRatio_mul_leftVariance
    (s : ℝ) (hs : 8 < s) (hcut : beta ≤ jointLeakageLossContractionCutoff s hs)
    (sources : List Link) (hNodup : sources.Nodup) (hComplete : ∀ e, e ∈ sources)
    (f : JL2) :
    (1 - jointLeakageLossRatio s beta) * ‖f - Cleft f‖ ^ 2 ≤
      realHilbertProjectionSweepPathLoss P sources f := by
  let S : JL2 → JL2 := realHilbertProjectionSweep P sources
  let D : ℕ → ℝ := fun n => ‖S^[n] f - Cleft (S^[n] f)‖ ^ 2
  let losses : ℕ → ℝ := fun n => realHilbertProjectionSweepPathLoss P sources (S^[n] f)
  have hLimit : Tendsto (fun n : ℕ => S^[n] f) atTop (𝓝 (Cleft f)) :=
    allLinkSweep_iterates_tendsto_leftRetained H N hN beta hbeta s hs hcut sources hNodup hComplete f
  have hIdem : Cleft (Cleft f) = Cleft f := congrArg
    (fun A : JL2 →L[ℝ] JL2 => A f) (allRightLeftRetained_idempotent H N hN beta hbeta)
  have hTail : Tendsto D atTop (𝓝 0) := by
    have hDiff := hLimit.sub ((Cleft.continuous.tendsto (Cleft f)).comp hLimit)
    simpa only [D, hIdem, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hDiff.norm.pow 2
  have hRenew : ∀ n : ℕ, D n = losses n + D (n + 1) := by
    intro n
    simpa only [D, losses, Function.iterate_succ_apply'] using
      allLinkSweep_leftRetained_pythagoras H N hN beta hbeta sources (S^[n] f)
  have hLoss : ∀ n : ℕ, losses (n + 1) ≤ jointLeakageLossRatio s beta * losses n := by
    intro n
    dsimp only [losses]
    rw [Function.iterate_succ_apply']
    exact allLinkSweep_pathLoss_le_lossRatio_mul H N hN beta hbeta s hs hcut sources hNodup hComplete (S^[n] f)
  simpa only [D, losses, Function.iterate_zero, id_eq] using
    RenewalTail.current_loss_controls_energy_of_tendsto_zero D losses (jointLeakageLossRatio s beta) hRenew hLoss hTail

/-- Volume/rank-independent Poincare relative to the complete retained left
boundary. The coefficient is exactly 1-2Q>0 on the EXISTING loss cutoff.
This is an unnormalized right-link inequality, not a physical-sector gap. -/
theorem allLink_relativePoincare
    (s : ℝ) (hs : 8 < s) (hcut : beta ≤ jointLeakageLossContractionCutoff s hs)
    (f : JL2) :
    (1 - 2 * jointLeakageSchurCoefficient s beta) * ‖f - Cleft f‖ ^ 2 ≤
      ∑ e : Link, ‖f - P e f‖ ^ 2 := by
  classical
  let sources : List Link := (Finset.univ : Finset Link).toList
  have hNodup : sources.Nodup := Finset.nodup_toList _
  have hComplete : ∀ e : Link, e ∈ sources := by intro e; simp [sources]
  have hMargin := allLinkSweep_pathLoss_ge_one_sub_lossRatio_mul_leftVariance
    H N hN beta hbeta s hs hcut sources hNodup hComplete f
  have hInitial := allLinkSweep_pathLoss_controlled_by_initialResidual H N hN beta hbeta s hs
    (hcut.trans (jointLeakageLossContractionCutoff_le_schurCutoff s hs)) sources hNodup f
  let q := jointLeakageSchurCoefficient s beta
  have hQ := jointLeakageSchurCoefficient_nonneg_lt_half s hs beta hbeta hcut
  have hDen : 1 - q ≠ 0 := ne_of_gt (by dsimp [q]; linarith [hQ.2])
  have hEtaMul : (1 - q) ^ 2 * jointLeakageLossRatio s beta = q ^ 2 := by
    change (1 - q) ^ 2 * (q / (1 - q)) ^ 2 = q ^ 2
    rw [div_pow]
    field_simp [hDen]
  have hCoeff : (1 - q) ^ 2 * (1 - jointLeakageLossRatio s beta) = 1 - 2 * q := by
    nlinarith [hEtaMul]
  calc
    _ = (1 - q) ^ 2 * ((1 - jointLeakageLossRatio s beta) * ‖f - Cleft f‖ ^ 2) := by
      rw [← mul_assoc, hCoeff]
    _ ≤ (1 - q) ^ 2 * realHilbertProjectionSweepPathLoss P sources f :=
      mul_le_mul_of_nonneg_left hMargin (sq_nonneg _)
    _ ≤ _ := hInitial

end GroundStateSourceFixedPairEnergy
end
end MGAP4D.MathlibAnalytic
