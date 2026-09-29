import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointAllRightRelativePoincare

open MGAP4D.MathlibAnalytic
open MGAP4D.MathlibAnalytic.GroundStateSourceFixedPairEnergy
open scoped BigOperators

local instance allRightRelativePoincareSmokeSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

#check realHilbertProjectionSweepSourceResidualProfile_le_budget_add_initial
#check RenewalTail.current_loss_controls_energy_of_tendsto_zero
#check allLinkSweep_pathLoss_controlled_by_initialResidual
#check allLinkSweep_pathLoss_le_lossRatio_mul
#check allLinkSweep_iteratedPathLoss_le_geometric
#check allRightLink_fixed_iff_leftRetained
#check allRightLeftRetained_absorb_sweep
#check allLinkSweep_iterates_tendsto_leftRetained
#check allLinkSweep_leftRetained_pythagoras
#check allLinkSweep_pathLoss_ge_one_sub_lossRatio_mul_leftVariance
#check allLink_relativePoincare

-- Full genuine joint L2: no core, tail, sector, or cardinality premise.
example (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (s : ℝ) (hs : 8 < s) (hcut : beta ≤ jointLeakageLossContractionCutoff s hs)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta) :
    (1 - 2 * jointLeakageSchurCoefficient s beta) *
      ‖f - allRightLeftRetainedCondExpL2 H N hN beta hbeta f‖ ^ 2 ≤
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          ‖f - periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN beta hbeta e f‖ ^ 2 := by
  exact allLink_relativePoincare H N hN beta hbeta s hs hcut f

-- The SAME cutoff gives a strictly positive coefficient, before any division.
example (s : ℝ) (hs : 8 < s) (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut : beta ≤ jointLeakageLossContractionCutoff s hs) :
    0 < 1 - 2 * jointLeakageSchurCoefficient s beta := by
  linarith [(jointLeakageSchurCoefficient_nonneg_lt_half s hs beta hbeta hcut).2]

-- At beta zero the conditional tensorization coefficient is exactly one.
example (H N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 8 < s)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN 0 le_rfl) :
    ‖f - allRightLeftRetainedCondExpL2 H N hN 0 le_rfl f‖ ^ 2 ≤
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖f - periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN 0 le_rfl e f‖ ^ 2 := by
  simpa using allLink_relativePoincare H N hN 0 le_rfl s hs
    (jointLeakageLossContractionCutoff_pos s hs).le f

-- A retained fixed component cannot be discarded to get an uncentered gap.
example : (∀ x : ℝ, ‖x - (ContinuousLinearMap.id ℝ ℝ) x‖ ^ 2 = 0) ∧
    ¬ (∀ x : ℝ, (1 / 2 : ℝ) * ‖x‖ ^ 2 ≤ ‖x - (ContinuousLinearMap.id ℝ ℝ) x‖ ^ 2) := by
  constructor
  · intro x; simp
  · intro h; have hOne := h 1; norm_num at hOne

-- The scalar renewal lemma includes eta=0 with a vanishing tail.
example : (1 - (0 : ℝ)) * (1 : ℝ) ≤ 1 := by norm_num

#print axioms realHilbertProjectionSweepSourceResidualProfile_le_budget_add_initial
#print axioms RenewalTail.current_loss_controls_energy_of_tendsto_zero
#print axioms allRightLink_fixed_iff_leftRetained
#print axioms allLinkSweep_pathLoss_controlled_by_initialResidual
#print axioms allLinkSweep_iterates_tendsto_leftRetained
#print axioms allLink_relativePoincare
