import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOrderedAllLinkSweepResidual

open MGAP4D.MathlibAnalytic
open MGAP4D.MathlibAnalytic.GroundStateSourceFixedPairEnergy
open scoped BigOperators

noncomputable section

local instance allLinkSweepSmokeSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

#check realHilbertProjectionSweepSourceResidualProfile
#check realHilbertProjectionSweepSourceResidualProfile_sq_sum_eq_pathLoss
#check realHilbertProjectionSweepTargetResidualForcingBudget_eq_weightedSourceProfile
#check sourceUpdate_targetResidual_norm_le_add_sourceResidual_allL2
#check allLinkSweep_targetResidual_le_orderedBudget_add_initial
#check allLinkSweep_targetResidual_le_orderedBudget_of_mem
#check allLinkSweep_orderedBudget_sq_sum_le_schurCoefficient_sq_mul_pathLoss
#check allLinkSweep_terminalResidual_sq_sum_le_schurCoefficient_sq_mul_pathLoss

-- All right links, arbitrary complete nodup order, arbitrary joint L2.
example (H N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta) (hcut : beta ≤ jointLeakageSchurCutoff s hs)
    (sources : List (PeriodicHypercubicEvenSpatialSliceLink H))
    (hNodup : sources.Nodup) (hComplete : ∀ t, t ∈ sources)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta) :
    let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2 H N hN beta hbeta
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      ‖realHilbertProjectionSweep P sources f - P target (realHilbertProjectionSweep P sources f)‖ ^ 2) ≤
      jointLeakageSchurCoefficient s beta ^ 2 * realHilbertProjectionSweepPathLoss P sources f := by
  exact allLinkSweep_terminalResidual_sq_sum_le_schurCoefficient_sq_mul_pathLoss
    H N hN s hs beta hbeta hcut sources hNodup hComplete f

-- A repeat is not silently discarded. With P=-id, both stage residuals are 2.
example : realHilbertProjectionSweepSourceResidualProfile
    (fun _ : Unit => -(ContinuousLinearMap.id ℝ ℝ)) [(), ()] 1 () = 4 := by
  norm_num [realHilbertProjectionSweepSourceResidualProfile]

example : (∑ t : Unit, realHilbertProjectionSweepSourceResidualProfile
      (fun _ : Unit => -(ContinuousLinearMap.id ℝ ℝ)) [(), ()] 1 t ^ 2) ≠
    realHilbertProjectionSweepPathLoss
      (fun _ : Unit => -(ContinuousLinearMap.id ℝ ℝ)) [(), ()] 1 := by
  norm_num [realHilbertProjectionSweepSourceResidualProfile, realHilbertProjectionSweepPathLoss]

-- The exact weighted identity permits negative weights and repeated sources.
example : realHilbertProjectionSweepTargetResidualForcingBudget
    (fun _ : Unit => -(ContinuousLinearMap.id ℝ ℝ))
    (fun _ x => (-3 : ℝ) * ‖x - (-(ContinuousLinearMap.id ℝ ℝ)) x‖) [(), ()] 1 = -12 := by
  norm_num [realHilbertProjectionSweepTargetResidualForcingBudget]

-- No target visit means the initial residual cannot be omitted.
example : ¬ (‖realHilbertProjectionSweep (fun _ : Unit => (0 : ℝ →L[ℝ] ℝ)) [] 1 -
      (0 : ℝ →L[ℝ] ℝ) (realHilbertProjectionSweep (fun _ : Unit => (0 : ℝ →L[ℝ] ℝ)) [] 1)‖ ^ 2 ≤
    (0 : ℝ) ^ 2 * realHilbertProjectionSweepPathLoss
      (fun _ : Unit => (0 : ℝ →L[ℝ] ℝ)) [] 1) := by
  norm_num [realHilbertProjectionSweep, realHilbertProjectionSweepPathLoss]

-- Zero coupling: the final full-sweep vector is fixed by every right link.
example (H N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 8 < s)
    (sources : List (PeriodicHypercubicEvenSpatialSliceLink H))
    (hNodup : sources.Nodup) (hComplete : ∀ t, t ∈ sources)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN 0 le_rfl) :
    let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2 H N hN 0 le_rfl
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      ‖realHilbertProjectionSweep P sources f - P target (realHilbertProjectionSweep P sources f)‖ ^ 2) = 0 := by
  have h := allLinkSweep_terminalResidual_sq_sum_le_schurCoefficient_sq_mul_pathLoss
    H N hN s hs 0 le_rfl (jointLeakageSchurCutoff_pos s hs).le sources hNodup hComplete f
  apply le_antisymm
  · simpa using h
  · exact Finset.sum_nonneg fun _ _ => sq_nonneg _

#print axioms realHilbertProjectionSweepTargetResidualForcingBudget_eq_weightedSourceProfile
#print axioms realHilbertProjectionSweepSourceResidualProfile_sq_sum_eq_pathLoss
#print axioms sourceUpdate_targetResidual_norm_le_add_sourceResidual_allL2
#print axioms allLinkSweep_targetResidual_le_orderedBudget_of_mem
#print axioms allLinkSweep_orderedBudget_sq_sum_le_schurCoefficient_sq_mul_pathLoss
#print axioms allLinkSweep_terminalResidual_sq_sum_le_schurCoefficient_sq_mul_pathLoss

end
