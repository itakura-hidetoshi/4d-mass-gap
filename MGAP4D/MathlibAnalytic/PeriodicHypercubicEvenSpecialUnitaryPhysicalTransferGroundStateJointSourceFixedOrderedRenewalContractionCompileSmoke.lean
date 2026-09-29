import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedOrderedRenewalContraction

open MGAP4D.MathlibAnalytic
open MGAP4D.MathlibAnalytic.GroundStateSourceFixedPairEnergy
open Filter
open scoped Topology

#check realHilbertProjectionSweep_displacement_le_length_mul_sqrt_pathLoss
#check realHilbertProjectionSweep_tendsto_block_of_geometric_pathLoss
#check fixedColor_iterates_tendsto_colorProjection
#check fixedColor_defect_iterates_tendsto_zero
#check fixedColor_nextDefect_le_lossRatio_mul
#check sixSpatial_nextDefectMean_le_lossRatio_mul
#check sixSpatial_terminalPathLoss_ge_one_sub_lossRatio_mul_defectMean

-- The physical theorem must have no externally supplied zero-tail hypothesis.
example (H N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut : beta ≤ jointLeakageLossContractionCutoff s hs)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta)
    (hf : f ∈ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore H N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
      H N hN beta hbeta color
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector H N hN beta hbeta color f)‖ ^ 2 ≤
      jointLeakageLossRatio s beta *
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector H N hN beta hbeta color f‖ ^ 2 := by
  exact fixedColor_nextDefect_le_lossRatio_mul H N hN beta hbeta s hs hcut color f hf

-- Empty sweeps and eta = 0 are included by the generic convergence theorem.
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P : Unit → E →L[ℝ] E) (x : E) :
    Tendsto (fun n : ℕ => (realHilbertProjectionSweep P [] : E → E)^[n] x)
      atTop (𝓝 x) := by
  simpa only [ContinuousLinearMap.id_apply] using
    (realHilbertProjectionSweep_tendsto_block_of_geometric_pathLoss
      P [] (ContinuousLinearMap.id ℝ E) 0 le_rfl (by norm_num)
      (fun _ => rfl) (fun _ _ => rfl) x (by
        intro n
        simp [realHilbertProjectionSweepPathLoss]))

-- Keep identical proof indices in all dependent beta-zero types.
example (H N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 8 < s)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN 0 le_rfl)
    (hf : f ∈ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore H N hN 0 le_rfl) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkNextSweepBlockDefectMeanNormSq
      H N hN 0 le_rfl f ≤ 0 := by
  have h := sixSpatial_nextDefectMean_le_lossRatio_mul H N hN 0 le_rfl s hs
    (jointLeakageLossContractionCutoff_pos s hs).le f hf
  simpa using h

#print axioms realHilbertProjectionSweep_displacement_le_length_mul_sqrt_pathLoss
#print axioms realHilbertProjectionSweep_tendsto_block_of_geometric_pathLoss
#print axioms fixedColor_iterates_tendsto_colorProjection
#print axioms fixedColor_defect_iterates_tendsto_zero
#print axioms fixedColor_nextDefect_le_lossRatio_mul
#print axioms sixSpatial_nextDefectMean_le_lossRatio_mul
#print axioms sixSpatial_terminalPathLoss_ge_one_sub_lossRatio_mul_defectMean
